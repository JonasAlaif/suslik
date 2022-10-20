package org.tygus.suslik.synthesis

import org.tygus.suslik.language.Expressions
import org.tygus.suslik.language.Expressions.{Expr, ExprSubst, Subst, SubstVar, Unknown, Var}
import org.tygus.suslik.language.Statements._
import org.tygus.suslik.logic.{FunSpec, Gamma, Heaplet, PFormula, SApp, RApp}
import org.tygus.suslik.logic.Specifications.{Assertion, Goal}
import org.tygus.suslik.synthesis.rules.BranchRules.Branch
import org.tygus.suslik.synthesis.rules.RuleUtils

/**
  * A continuation that builds a solution for a synthesis problem
  * from solutions of its sub-problems
  */
sealed abstract class StmtProducer extends RuleUtils {
  val exceptionQualifier: String = "producer"

  val arity: Int
  val fn: Kont

  def apply(children: Seq[Solution]): Solution = {
    ruleAssert(children.lengthCompare(arity) == 0, s"Producer expects $arity children and got ${children.length}")
    fn(children)
  }

  def >>(p: StmtProducer): StmtProducer = StmtProducerOps.>>(this, p)

  def liftToSolutions(f: Seq[Statement] => Statement)(arg: Seq[Solution]): Solution = {
    val (stmts, helpers) = arg.unzip
    val stmt = f(stmts)
    val allHelpers = helpers.toList.flatten
    (stmt, allHelpers)
  }

}

object StmtProducerOps {
  /**
    * Producer transformer that sequences two producers:
    * the resulting producer first applies p1 to a prefix of child solutions,
    * then applies p2 to the result of p1 and a suffix of child solutions
    */
  case class >>(p1: StmtProducer, p2: StmtProducer) extends StmtProducer {
    val arity: Int = p1.arity + p2.arity - 1
    val fn: Kont = sols => {
      val (sols1, sols2) = sols.splitAt(p1.arity)
      val sol = p1.fn(sols1)
      p2.fn(sol +: sols2)
    }
  }
}

/**
  * Identity producer: returns the first child solution unchanged
  */
case object IdProducer extends StmtProducer {
  val arity: Int = 1
  val fn: Kont = _.head
}

/**
  * Constant producer: ignored child solutions and returns s
  */
case class ConstProducer(s: Statement) extends StmtProducer {
  val arity: Int = 0
  val fn: Kont = liftToSolutions(_ => s.simplify)
}

/**
  * Producer that prepends s to the first child solution
  */
case class PrependProducer(s: Statement) extends StmtProducer {
  val arity: Int = 1
  val fn: Kont = liftToSolutions(stmts => {
    SeqComp(s.simplify, stmts.head).simplify
  })
}

/**
  * Same as prepend but do not simplify s away, because it comes from the sketch
  */
case class PrependFromSketchProducer(s: Statement) extends StmtProducer {
  val arity: Int = 1
  val fn: Kont = liftToSolutions(stmts => {
    SeqComp(s.simplify, stmts.head).simplify
  })
}

/**
  * Producer that appends s to the first child solution
  */
case class AppendProducer(s: Statement) extends StmtProducer {
  val arity: Int = 1
  val fn: Kont = liftToSolutions(stmts => {
    SeqComp(stmts.head, s.simplify).simplify
  })
}

/**
  * Producer that sequentially composes results of two goals
  */
case object SeqCompProducer extends StmtProducer {
  val arity: Int = 2
  val fn: Kont = liftToSolutions(stmts => {
    SeqComp(stmts.head, stmts.last).simplify
  })
}

/**
  * Producer that checks if the child solution has backlinks to its goal,
  * and if so produces a helper call and a new helper
  */
case class ExtractHelper(goal: Goal) extends StmtProducer {
  val arity: Int = 1
  val fn: Kont = sols => {
    val (stmt, helpers) = sols.head
    if (stmt.companions.contains(goal.label) && !goal.isTopLevel) {
      val f = goal.toFunSpec
      // Substitute all unknowns with true
      val finalized = (f.pre.phi.unknowns ++ f.post.phi.unknowns).foldLeft(f)({case (spec, u) => spec.substUnknown(Map(u -> Expressions.eTrue))})
      val (newHelper, newCall) = Procedure(finalized, stmt, finalized.toCall)(goal.env.predicates)
      // TODO: CopyOut substitution will not be copied across a call boundary!
      (newCall, newHelper :: helpers)
    } else
      (stmt, helpers)
  }
}

// Produces a conditional that branches on the selectors
case class BranchProducer(results: Results, freshVars: SubstVar, sbst: Subst, selectors: Seq[Expr]) extends StmtProducer {
  val arity: Int = selectors.length
  val fn: Kont = liftToSolutions(stmts => {
    if (stmts.length == 1) stmts.head else {
      val cond_branches = selectors.zip(stmts).reverse
      val ctail = cond_branches.tail
      val finalBranch = cond_branches.head._2
      ctail.foldLeft(finalBranch) { case (eb, (c, tb)) =>
        If(results, c, tb, eb).simplify
      }
    }
  })
}

// Produces a conditional that branches on the selectors
case class MatchProducer(results: Results, tgt: Var, pred: String, freshVars: SubstVar, subst: Subst, selectors: Seq[(Option[String], Seq[Var])]) extends StmtProducer {
  val arity: Int = selectors.length
  val fn: Kont = if (this.arity == 1) SubstMapProducer(subst).fn else liftToSolutions(stmts => {
    val cond_branches = selectors.map(s => s._1 ->
      (s._2)).zip(stmts)
    val arms = cond_branches.map { case ((variant, fields), stmt) =>
      (Construct(None, pred, variant, fields.map(f => f -> freshVars(f))),
        stmt)
    }
    Match(results, tgt, arms).simplify
  })
}

// Joins a guarded statement and an else-branch into a conditional,
// if goal is the right branching point (otherwise simply propagates the guarded statement)
case class GuardedBranchProducer(goal: Goal, unknown: Unknown) extends StmtProducer {
  val arity: Int = 2
  val fn: Kont = liftToSolutions(stmts => {
    stmts.head match {
      case Guarded(cond, body) if Branch.isBranchingPoint(goal, cond)
      => If(???, cond, body, stmts.last).simplify // Current goal is the branching point: create conditional
      case stmt => stmt // Current goal is not the branching point: second child is always vacuous, so ignore it
    }
  })
}

// Creates a guarded statement with condition cond
case class GuardedProducer(cond: Expr) extends StmtProducer {
  val arity: Int = 1
  val fn: Kont = liftToSolutions(stmts => Guarded(cond, stmts.head).simplify)
}

trait Noop {
  val arity: Int = 1
  val fn: Kont = _.head
}

case class CrossFnSubstProducer(from: Var, to: Expr) extends StmtProducer {
  val arity: Int = 1
  val fn: Kont = sols => {
    val (stmt, helpers) = sols.head
    val vars = stmt.vars
    val (to_sub, other) = helpers.partition(h => vars(Var(h.name)))
    val sub = Sub(Map(from -> to))
    (SeqComp(sub, stmt).simplify, to_sub.map(_.subst(sub)) ++ other)
  }
}
// Captures variable to expression substitutions
case class SubstProducer(from: Var, to: Expr) extends StmtProducer {
  val arity: Int = 1
  val fn: Kont = liftToSolutions(stmts => {
    SeqComp(Sub( Map(from -> to) ), stmts.head).simplify
  })
}
case class SubstMapProducer(subst: Subst) extends StmtProducer {
  val arity: Int = 1
  val fn: Kont = liftToSolutions(stmts => {
    SeqComp(Sub(subst).simplify, stmts.head).simplify
  })
}

// Captures variable to variable substitutions
case class SubstVarProducer(from: Var, to: Var) extends StmtProducer with Noop

// Captures an unfolded predicate application
case class UnfoldProducer(app: SApp, selector: Expr, asn: Assertion, substEx: SubstVar) extends StmtProducer with Noop

// Abduce Call
case class AbduceCallProducer(f: FunSpec) extends StmtProducer {
  val arity: Int = 1
  val fn: Kont = liftToSolutions(stmts => {
    stmts.head match {
      case c: Call => SeqComp(c.callGoal, c.copy(callGoal = Hole)).simplify
      case SeqComp(c: Call, s2) =>
        SeqComp(SeqComp(c.callGoal, c.copy(callGoal = Hole)).simplify, s2).simplify
      case Error => Error
    }
  })
}

// Captures entailments emitted by SMT
case class PureEntailmentProducer(prePhi: PFormula, postPhi: PFormula, gamma: Gamma) extends StmtProducer with Noop

// Captures heap unifications
case class UnificationProducer(preHeaplet: Heaplet, postHeaplet: Heaplet, subst: ExprSubst) extends StmtProducer with Noop

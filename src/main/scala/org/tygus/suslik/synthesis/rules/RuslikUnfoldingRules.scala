package org.tygus.suslik.synthesis.rules

import org.tygus.suslik.language.Expressions._
import org.tygus.suslik.language.Statements._
import org.tygus.suslik.language.{CardType, Ident}
import org.tygus.suslik.logic.Specifications._
import org.tygus.suslik.logic._
import org.tygus.suslik.logic.smt.SMTSolving
import org.tygus.suslik.report.ProofTrace
import org.tygus.suslik.synthesis.Termination.Transition
import org.tygus.suslik.synthesis._
import org.tygus.suslik.synthesis.rules.Rules._

/**
  * Unfolding rules deal with Rust predicates and recursion.
  *
  * @author Jonas Fiala
  */

object RuslikUnfoldingRules extends SepLogicUtils with RuleUtils {
  val exceptionQualifier: String = "rule-unfolding"

  def loadPred(rapp: RApp, vars: Set[Var], predicates: PredicateEnv, isPre: Boolean): (Seq[InductiveClause], Subst, SubstVar) = {
    assert(!isPre || rapp.blocked.getNamed.isEmpty)
    val ip = predicates(rapp.pred)
    assert(ip.params.length == rapp.fnSpec.length)
    val args_subst = ip.params.map(_._1).zip(rapp.fnSpec).toMap
    // Functional values should never accidentally alias (an existential RApp in the post should remain so)
    val prePostUniq = if (isPre) "O" else "F"
    val existentials_subst = ip.existentials.map(e => e -> Var(e.name + "_" + rapp.field.name + prePostUniq)).toMap
    // Fields should always alias (so that refs match up in pre/post)
    val fields_subst = ip.fields.map(e => e -> Var(e.name + "_" + rapp.field.name)).toMap
    val subst = args_subst ++ existentials_subst ++ fields_subst
    val newIp = ip.clauses.map(c => InductiveClause(c.selector.subst(subst), c.asn.subst(subst).setTagAndRef(rapp)))

    (newIp, args_subst, existentials_subst ++ fields_subst)
  }

  def loadPrimPred(rapp: RApp, vars: Set[Var], predicates: PredicateEnv): Assertion = {
    // There should be no existentials in a primitive pred (so `isPre` is irrelevant)
    val (pred_clauses, _, subst) = loadPred(rapp, vars, predicates, true)
    assert(subst.isEmpty)
    assert(pred_clauses.length == 1)
    pred_clauses.head.asn
  }

  /*
  Copy out rule: load in a primitive value
   */
  object CopyOut extends SynthesisRule with GeneratesCode with InvertibleRule {
    override def toString: Ident = "CopyOut"

    def apply(goal: Goal): Seq[RuleResult] = {
      // Prevent repeatedly copying out from borrows
      def loadVars(rapp: RApp): Seq[Var] =
        for { v@Var(_) <- rapp.fnSpec; if !goal.programVars.contains(v) } yield v
      // Take first prim, we will unfold all anyway
      val prims = goal.pre.sigma.prims(goal.env.predicates).filter(h => !h.priv && !h.isBlocked && !loadVars(h).isEmpty)
      if (prims.length == 0) return Seq()
      val prim = prims.head
      val asn = loadPrimPred(prim, goal.vars, goal.env.predicates)
      val newVars = loadVars(prim)
      val newGoal = goal.spawnChild(
        Assertion(goal.pre.phi && asn.phi, goal.pre.sigma),
        programVars = goal.programVars ++ newVars
      )
      assert(newVars.length == 1)
      val field = if (prim.isBorrow) UnaryExpr(OpDeRef, prim.field) else prim.field
      val kont = SubstProducer(newVars.head, field)
      Seq(RuleResult(List(newGoal), kont, this, goal))
    }
  }

  /*
  Open rule: unroll a predicate in the pre-state
   */
  object Open extends SynthesisRule with GeneratesCode {

    override def toString: Ident = "Open"

    def apply(goal: Goal): Seq[RuleResult] = {
      for {
        (h, c, isCyc) <- goal.constraints.canUnfoldPre(goal)
        // TODO: these checks are redundant (done in canUnfoldPre)
        if !h.priv && !h.isBlocked // Must be non-private and non-blocked
        // Only for non-primitive types
        if !h.isPrim(goal.env.predicates)
        if h.tag.unrolls < goal.env.config.maxOpenDepth
      } yield {
        val (clauses, sbst, fresh_subst) = loadPred(h, goal.vars, goal.env.predicates, true)
        val newGoals = clauses.zipWithIndex.map { case (clause, j) => {
          val newVars = clause.asn.sigma.rapps.map(_.field)
          goal.spawnChild(
            pre = Assertion(goal.pre.phi && clause.asn.phi && clause.selector, goal.pre.sigma ** clause.asn.sigma - h),
            constraints = c,
            programVars = goal.programVars ++ newVars,
            childId = Some(j),
            // True since we might satisfy the call termination requirement now
            hasProgressed = true,
            // If we reborrowed cannot be a companion since the borrows won't match up (need to expire first)
            isCompanion = !h.isBorrow)
        }}
        // TODO: this shouldn't be a flatMap (e.g. if fields in different branches alias)
        val nameSubs = goal.env.predicates(h.pred).clauses.flatMap(
          _.asn.sigma.rapps.map(a => Var(a.field.name + "_" + h.field.name) -> BinaryExpr(OpField, h.field, a.field))
        ).toMap
        val nSubsRef = if (h.isBorrow) nameSubs.map(m => m._1 -> UnaryExpr(OpTakeRef, m._2)) else nameSubs
        val kont = BranchProducer(Some(h.toSApp), fresh_subst, sbst, clauses.map(_.selector)) >>
          SubstMapProducer(nSubsRef) >> ExtractHelper(goal)
        RuleResult(newGoals, kont, this, goal)
      }
    }
  }

  object AbduceCall extends SynthesisRule {

    override def toString: Ident = "TryCall"

    def apply(goal: Goal): Seq[RuleResult] = {
      val cands = goal.companionCandidates
      val funLabels = cands.map(a => (a.toFunSpec, Some(a.label))) ++ // companions
        goal.env.functions.values.map(f => (f, None)) // components
      for {
        (_f, l) <- funLabels
        (freshSub, f) = _f.refreshAll(goal.vars)

        // Optimization: do not consider f if its pre has predicates that cannot possibly match ours
        if multiSubset(f.pre.sigma.profile.apps, goal.pre.sigma.profile.apps)
        if (goal.env.config.maxCalls :: goal.pre.sigma.callTags).min < goal.env.config.maxCalls
      } yield {
        val newGamma = goal.gamma ++ (f.params ++ f.var_decl).toMap // Add f's (fresh) variables to gamma
        val call = Call(Var(f.name), f.result, f.params.map(_._1), l)
        val calleePostSigma = f.post.sigma.setSAppTags(PTag(1, 0))
        val callePost = Assertion(f.post.phi, calleePostSigma)
        val suspendedCallGoal = Some(SuspendedCallGoal(goal.pre, goal.post, callePost, call, freshSub))
        val newGoal = goal.spawnChild(post = f.pre, gamma = newGamma, callGoal = suspendedCallGoal)
        val kont: StmtProducer = AbduceCallProducer(f) >> ExtractHelper(goal)

        ProofTrace.current.add(ProofTrace.DerivationTrail(goal, Seq(newGoal), this,
          Map("fun" -> f.name, "args" -> f.params.map(_._1.pp))))

        RuleResult(List(newGoal), kont, this, goal)
      }
    }
  }


  /*
  Close rule: unroll a predicate in the post-state
   */
  object Close extends SynthesisRule {

    override def toString: Ident = "Close"

    def apply(goal: Goal): Seq[RuleResult] = {
      for {
        // TODO: Could potentially be a create-borrow rule as well for local lifetimes
        (h, c) <- goal.constraints.canUnfoldPost(goal)
        // TODO: we might get stuck here
        // (canUnfoldPost only returns non-cyclic, but none of those are unfoldable, so can never get to unfolding non-cyclic)
        if h.tag.unrolls < goal.env.config.maxCloseDepth
        val (clauses, _, fresh_subst) = loadPred(h, goal.vars, goal.env.predicates, false)
        InductiveClause(selector, asn) <- clauses
        if asn.sigma.rapps.filter(_.priv).length == (if (clauses.length > 1) 1 else 0)
      } yield {
        assert(!h.isBlocked)
        // TODO: hacky way to remove discriminant
        val noDisc = SFormula(asn.sigma.chunks.filter {
          case RApp(true, _, _, _, _, _, _) => false
          case _ => true
        })
        val newPost = Assertion(
          goal.post.phi && asn.phi && selector,
          goal.post.sigma ** noDisc - h
        )
        val construct_args = if (h.isPrim(goal.env.predicates)) h.fnSpec else asn.sigma.rapps.map(_.field)
        val kont =
          UnfoldProducer(h.toSApp, selector, Assertion(asn.phi, asn.sigma), fresh_subst) >>
          AppendProducer(Construct(h.field, h.pred, construct_args)) >>
          ExtractHelper(goal)
        RuleResult(List(goal.spawnChild(post = newPost, constraints = c,
            // Hasn't progressed since we didn't progress toward termination
            // Could be used as a companion, but currently won't since it isn't possible to make progess after closing (no more open)
            hasProgressed = false, isCompanion = true)), kont, this, goal)
      }
    }
  }

  /*
  Expire rule: expire a reborrow in the post-state
   */
  abstract class Expire extends SynthesisRule {

    override def toString: Ident = "Expire"

    def filter(r: RApp, goal: Goal): Boolean
    def apply(goal: Goal): Seq[RuleResult] = {
      val preBorrows = goal.pre.sigma.borrows.map(_.field)
      for {
        h <- goal.post.sigma.borrows
        // Expire non-writable borrows eagerly
        if filter(h, goal)
        // Cannot expire existential
        if !goal.existentials.contains(h.field)
        // Cannot expire before reborrowing:
        if !preBorrows.contains(h.field)
        val (clauses, sbst, fresh_subst) = loadPred(h, goal.vars, goal.env.predicates, false)
        InductiveClause(selector, asn) <- clauses
        // Hacky way to ensure we can only Expire the correct enum variant:
        if clauses.length == 1 || {
          val sel = selector.asInstanceOf[BinaryExpr]
          val disc = asn.sigma.rapps.find(d => d.fnSpec.length == 1 && d.fnSpec.head == sel.left).get
          val pre_disc = goal.pre.sigma.rapps.find(_.field == disc.field).get
          if (pre_disc.fnSpec.length != 1) println("Found: " + pre_disc.pp)
          assert(pre_disc.fnSpec.length == 1)
          pre_disc.fnSpec.head.asInstanceOf[Const] == sel.right
        }
        (phi, sigma) = if (clauses.length == 1) (asn.phi, asn.sigma) else {
          val sel = selector.asInstanceOf[BinaryExpr]
          val disc = asn.sigma.rapps.find(d => d.fnSpec.length == 1 && d.fnSpec.head == sel.left).get
          (asn.phi, asn.sigma ** disc.subst(sel.left.asInstanceOf[Var], sel.right) - disc)
        }
        // If I'm blocked, one of my children must've been blocked
        sigmaWithBlock <- if (!h.isBlocked) Seq(sigma)
          else sigma.rapps.map(r => (sigma - r) ** r.copy(blocked = h.blocked))
      } yield {
        val newPost = Assertion(
          goal.post.phi && phi,
          goal.post.sigma ** sigmaWithBlock - h
        )
        RuleResult(List(goal.spawnChild(post = newPost,
            // Hasn't progressed since we didn't progress toward termination, but can be companion
            hasProgressed = false, isCompanion = true)), IdProducer, this, goal)
      }
    }
  }
  object ExpireNoWrite extends Expire {
    override def filter(r: RApp, goal: Goal): Boolean = !goal.isRAppExistential(r)
  }
  object ExpireFinal extends Expire with InvertibleRule {
    override def filter(r: RApp, goal: Goal): Boolean = goal.isRAppExistential(r)
  }

  /*
  Unify lfts rule: drop a borrow in the post
   */
  object UnifyLft extends SynthesisRule {

    override def toString: Ident = "UnifyLft"

    def apply(goal: Goal): Seq[RuleResult] = {
      val preBorrows = goal.pre.sigma.borrows.map(_.field)
      for {
        h <- goal.post.sigma.borrows
        // Only unify if cannot expire:
        if preBorrows.contains(h.field)
        b <- h.blocked.getNamed
      } yield {
        val newPost = Assertion(
          goal.post.phi && (h.ref.get.lft.getNamed.get.name |=| b.name).simplify,
          goal.post.sigma - h
        )
        RuleResult(List(goal.spawnChild(post = newPost,
            // Hasn't progressed since we didn't progress toward termination, but can be companion
            hasProgressed = false, isCompanion = true)), ExtractHelper(goal), this, goal)
      }
    }
  }

  /*
  Borrow write rule: write to a borrow in the post-state
   */
  object BrrwWrite extends SynthesisRule {

    override def toString: Ident = "BrrwWrite"

    def apply(goal: Goal): Seq[RuleResult] = {
      val post = goal.post
      val env = goal.env

      for {
        brrw <- goal.post.sigma.borrows
        if !goal.isRAppExistential(brrw) //brrw.isWriteableBorrow(goal.existentials)
      } yield {
        val newOwned = brrw.copy(field = Var(brrw.field.name + "_NV"), ref = None)
        val newBrrw = brrw.copy(fnSpec = brrw.fnSpec.zipWithIndex.map(i => Var(brrw.field.pp + i._2)))
        val newPost = Assertion(post.phi, (post.sigma ** newOwned - brrw) ** newBrrw)

        val kont = AppendProducer(Store(brrw.field, 0, newOwned.field))
        RuleResult(List(goal.spawnChild(post = newPost)), kont, this, goal)
      }
    }
  }
}

package org.tygus.suslik.synthesis.rules

import org.tygus.suslik.language.Statements.Solution
import org.tygus.suslik.logic.Specifications.Goal
import org.tygus.suslik.logic._
import org.tygus.suslik.synthesis.StmtProducer
import org.tygus.suslik.synthesis.Termination.Transition

object Rules {

  // Function that updates a goal based on solutions generated by its succeeded and-siblings
  type GoalUpdater = Seq[Solution] => Goal => Goal

  /**
    * Result of a rule application:
    * sub-goals to be solved and
    * a statement producer that assembles the sub-goal results
    */
  case class RuleResult(subgoals: Seq[Goal],
                        producer: StmtProducer,
                        rule: SynthesisRule,
                        transitions: Seq[Transition],
                        updates: Seq[GoalUpdater])

  object RuleResult {
    // Trivial update that ignores sibling solutions
    def noUpdate: GoalUpdater = Function.const(identity)

    def apply(subgoals: Seq[Goal], producer: StmtProducer, rule: SynthesisRule, goal: Goal) =
      new RuleResult(subgoals, producer, rule, subgoals.map(sub => Transition(goal, sub)),
        Seq.fill(subgoals.size){noUpdate})

    def apply(subgoals: Seq[Goal], producer: StmtProducer, rule: SynthesisRule, transitions: Seq[Transition]) =
      new RuleResult(subgoals, producer, rule, transitions,
        Seq.fill(subgoals.size){noUpdate})

  }


  /**
    * A generic class for a deductive rule to be applied
    *
    * @author Ilya Sergey
    */
  abstract class SynthesisRule extends PureLogicUtils {
    // Apply the rule and get all possible sub-derivations
    def apply(goal: Goal): Seq[RuleResult]
  }

  /**
    * Different kinds of rules
    */

  // Invertible rule: does not restrict the set of derivations,
  // so no need to backtrack in case of failure
  trait InvertibleRule

  // This rule produces code
  trait GeneratesCode

  trait PhaseDisabled {
    def heapletFilter(h: Heaplet): Boolean = true

    def profilesMatch(pre: SFormula, post: SFormula, exact: Boolean): Boolean = true
  }

  trait UnfoldingPhase {
    def heapletFilter(h: Heaplet, post: SFormula): Boolean = {
      h.isInstanceOf[SApp]
    }

    def profilesMatch(pre: SFormula, post: SFormula, exact: Boolean): Boolean = {
      if (exact) pre.profile.apps == post.profile.apps else multiSubset(post.profile.apps, pre.profile.apps)
    }
  }

  trait BlockPhase {
    // This must be the first block heaplet in the post (this is a focusing technique)
    def heapletFilter(h: Heaplet, post: SFormula): Boolean = {
      h.isInstanceOf[Block] && post.chunks.filter(_.isInstanceOf[Block]).indexOf(h) == 0
    }

    def profilesMatch(pre: SFormula, post: SFormula, exact: Boolean): Boolean = {
//      if (exact) pre.profile.blocks == post.profile.blocks else multiSubset(post.profile.blocks, pre.profile.blocks)
      true // In the block phase we don't require them to match, because of how free and alloc are triggered
    }
  }

  trait FlatPhase {
    // This must be the first heaplet in the post (this is a focusing technique)
    def heapletFilter(h: Heaplet, post: SFormula): Boolean = post.chunks.indexOf(h) == 0

    def profilesMatch(pre: SFormula, post: SFormula, exact: Boolean): Boolean = {
      if (exact) pre.profile.ptss == post.profile.ptss else multiSubset(post.profile.ptss, pre.profile.ptss)
    }
  }

  // Multiset inclusion
  def multiSubset[A](m1: Map[A, Int], m2: Map[A, Int]): Boolean =
    m1.forall { case (k, v) => v <= m2.getOrElse(k, 0) }

  def nubBy[A,B](l:List[A], p:A=>B):List[A] =
  {
    def go[A,B](l:List[A], p:A=>B, s:Set[B], acc:List[A]):List[A] = l match
    {
      case Nil => acc.reverse
      case x::xs if s.contains(p(x)) => go(xs,p,s,acc)
      case x::xs                     => go(xs,p,s+p(x),x::acc)
    }
    go(l,p,Set.empty,Nil)
  }
}

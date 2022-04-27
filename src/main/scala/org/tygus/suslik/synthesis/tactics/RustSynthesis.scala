package org.tygus.suslik.synthesis.tactics

import org.tygus.suslik.logic.Specifications.Goal
import org.tygus.suslik.synthesis.SearchTree.OrNode
import org.tygus.suslik.synthesis.SynConfig
import org.tygus.suslik.synthesis.rules.Rules.SynthesisRule
import org.tygus.suslik.synthesis.rules._
import org.tygus.suslik.util.SynStats

abstract class RustSynthesis (config: SynConfig) extends Tactic {

  def nextRules(node: OrNode): List[SynthesisRule] = {
    val goal = node.goal
    if (!goal.pre.sigma.prims.isEmpty) List(RuslikUnfoldingRules.Open)
    else if (!goal.post.sigma.prims.isEmpty) List(RuslikUnfoldingRules.Close)
    else if (!goal.pre.sigma.ghosts.isEmpty) List(RuslikUnfoldingRules.Open, RuslikUnfoldingRules.Reborrow)
    else if (!goal.post.sigma.ghosts.isEmpty) List(RuslikUnfoldingRules.Close)
    // Might still be solvable by "Inconsistency"
    else if (goal.isUnsolvable) anyPhaseRules
    else if (goal.callGoal.nonEmpty) callAbductionRules(goal)
    else anyPhaseRules ++ specBasedRules(node)
  }

  protected def callAbductionRules(goal: Goal): List[SynthesisRule] = {
  List(
      UnificationRules.SubstRight,
      // FailRules.PostInconsistent,
      // FailRules.CheckPost
      ) ++
      (if (goal.post.sigma.apps.nonEmpty)
        List(LogicalRules.FrameUnfoldingFinal,
          UnificationRules.HeapUnifyUnfolding)
      else
        List(UnfoldingRules.CallRule,
          UnificationRules.SubstRight,
          // LogicalRules.FrameFlat,
          // UnificationRules.PickCard,
          // LogicalRules.GhostWrite,
          // UnificationRules.HeapUnifyPure,
          // LogicalRules.SimplifyConditional,
          // OperationalRules.WriteRule,
          UnificationRules.Pick
          ))
  }

  protected def anyPhaseRules: List[SynthesisRule] = List(
    LogicalRules.Inconsistency,
    // LogicalRules.SubstLeft,
    UnificationRules.SubstRight,
  )

  protected def specBasedRules(node: OrNode): List[SynthesisRule] = {
    val goal = node.goal
    if (!goal.post.sigma.borrows.isEmpty) {
      // Borrows phase: get rid of borrows
      val lastUnfoldingRule = node.ruleHistory.dropWhile(anyPhaseRules.contains).headOption
      if (lastUnfoldingRule.contains(UnificationRules.HeapUnifyBorrows) ||
        lastUnfoldingRule.contains(LogicalRules.FrameBorrows) ||
        lastUnfoldingRule.contains(LogicalRules.FrameBorrowsFinal))
        List(
          LogicalRules.FrameBorrowsFinal,
          UnificationRules.HeapUnifyBorrows,
        )
      else List(
        LogicalRules.FrameBorrows,
        UnificationRules.HeapUnifyBorrows,
        RuslikUnfoldingRules.AbduceCall,
        RuslikUnfoldingRules.Reborrow,
        RuslikUnfoldingRules.BrrwWrite,
      )
    }
    else if (goal.post.hasPredicates) {
      // Unfolding phase: get rid of predicates
      val lastUnfoldingRule = node.ruleHistory.dropWhile(anyPhaseRules.contains).headOption
      if (lastUnfoldingRule.contains(UnificationRules.HeapUnifyUnfolding) ||
        lastUnfoldingRule.contains(LogicalRules.FrameUnfolding) ||
        lastUnfoldingRule.contains(LogicalRules.FrameUnfoldingFinal))
        List(
          LogicalRules.FrameUnfoldingFinal,
          UnificationRules.HeapUnifyUnfolding,
        )
      else if (lastUnfoldingRule.contains(RuslikUnfoldingRules.Close))
        List(
          LogicalRules.FrameUnfoldingFinal,
          UnificationRules.HeapUnifyUnfolding,
          RuslikUnfoldingRules.Close,
        )
      else List(
        LogicalRules.FrameUnfolding,
        UnificationRules.HeapUnifyUnfolding,
        RuslikUnfoldingRules.AbduceCall,
        RuslikUnfoldingRules.Open,
        RuslikUnfoldingRules.Close,
      )
    } else {
      List(
        LogicalRules.EmpRule,
        UnificationRules.Pick,
      )
    }
  } 

}

class AutomaticRust(config: SynConfig) extends RustSynthesis(config) with AutomaticSynthesis
class InteractiveRust(config: SynConfig, override val stats: SynStats) extends RustSynthesis(config) with InteractiveSynthesis

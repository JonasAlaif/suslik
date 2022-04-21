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
    if (goal.isUnsolvable)
      Nil
    else if (goal.callGoal.nonEmpty) callAbductionRules(goal)
    else anyPhaseRules ++ specBasedRules(node)
  }

  protected def callAbductionRules(goal: Goal): List[SynthesisRule] = {
    List()
  }

  protected def anyPhaseRules: List[SynthesisRule] = List(
    LogicalRules.Inconsistency,
    // LogicalRules.SubstLeft,
    UnificationRules.SubstRight,
  )

  protected def specBasedRules(node: OrNode): List[SynthesisRule] = {
    val goal = node.goal
    if (goal.hasPredicates()) {
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
        // RuslikUnfoldingRules.AbduceCall,
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

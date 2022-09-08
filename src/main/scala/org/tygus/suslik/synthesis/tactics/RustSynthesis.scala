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
    // Might still be solvable by "Inconsistency"
    if (goal.isUnsolvable) List(LogicalRules.Inconsistency)
    else if (goal.callGoal.nonEmpty) callAbductionRules(goal)
    else anyPhaseRules ++ specBasedRules(node)
  }

  protected def callAbductionRules(goal: Goal): List[SynthesisRule] = {
  List(
      UnificationRules.SubstRight,
      // FailRules.PostInconsistent,
      // FailRules.CheckPost
      ) ++
      (if (goal.post.sigma.rapps.nonEmpty)
        List(RuslikUnfoldingRules.NonTermCall,
          LogicalRules.FrameBorrowsFinal,
          UnificationRules.HeapUnifyBorrows,
          RuslikUnfoldingRules.Close,
          RuslikUnfoldingRules.ReborrowCall)
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
    RuslikUnfoldingRules.AddToPost,
    RuslikUnfoldingRules.KillLft,
    LogicalRules.SubstLeft,
    UnificationRules.SubstRight,
    LogicalRules.CaseSplit,
    RuslikUnfoldingRules.CopyOut,
    RuslikUnfoldingRules.ExpireFinal,
    RuslikUnfoldingRules.OpenInv,
    // FailRules.PostInconsistent,
  )

  protected def specBasedRules(node: OrNode): List[SynthesisRule] = {
    val goal = node.goal
    if (!goal.post.sigma.rapps.isEmpty) {
      // Unfolding phase: get rid of predicates
      val historySinceCall = node.ruleHistory.takeWhile(_ != UnfoldingRules.CallRule)
      // Started Unifying/Framing
      if (historySinceCall.exists(rule =>
        rule == UnificationRules.HeapUnifyBorrows ||
        rule == LogicalRules.FrameBorrows ||
        rule == LogicalRules.FrameBorrowsFinal
      ))
        List(
          LogicalRules.FrameBorrowsFinal,
          UnificationRules.HeapUnifyBorrows,
        )
      // TODO: there is an optimization here that is not always complete, this might cause issues
      else if (goal.isProbablyUnsolvable) List()
      else
        List(
          LogicalRules.FrameBorrows,
          UnificationRules.HeapUnifyBorrows,
          RuslikUnfoldingRules.Open,
          RuslikUnfoldingRules.AbduceCall,
          RuslikUnfoldingRules.Close,
          RuslikUnfoldingRules.Reborrow,
          RuslikUnfoldingRules.ExpireNoWrite,
          RuslikUnfoldingRules.BrrwWrite,
        )
    } else {
      List(
        RuslikUnfoldingRules.CannotConstruct,
        RuslikUnfoldingRules.Drop,
        LogicalRules.EmpRule,
        UnificationRules.Pick,
      )
    }
  } 

}

class AutomaticRust(config: SynConfig) extends RustSynthesis(config) with AutomaticSynthesis
class InteractiveRust(config: SynConfig, override val stats: SynStats) extends RustSynthesis(config) with InteractiveSynthesis

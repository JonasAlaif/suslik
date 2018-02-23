package org.tygus.synsl.logic.entailment

import org.tygus.synsl.language.Expressions.Var
import org.tygus.synsl.logic._

/**
  * @author Ilya Sergey
  */

trait EntailmentRules extends PureLogicUtils {

  /*
    TODO: Unify the definitions below with synthesis machinery,
    as discussed on Feb 13, 2018.
   */
  abstract sealed class EntRuleResult

  case object EntFail extends EntRuleResult

  case class EntMoreGoals(goals: List[Spec]) extends EntRuleResult

  abstract class EntailmentRule {
    def apply(spec: Spec, env: Environment): EntRuleResult
  }

  // ======================================================== //
  // So far, handling only conjunction with equalities

  /* *********************************************************
   * NORMALIZATION RULES
   * *********************************************************/

  // So far, handling only conjunction with equalities

  // [Substitution]
  object Substitution extends EntailmentRule {
    override def toString: String = "[Norm: Substitution]"

    def apply(spec: Spec, env: Environment): EntRuleResult = {
      val Spec(Assertion(p1, s1), Assertion(p2, s2), g) = spec

      findConjunctAndRest({
        case PEq(a@Var(_), b) => a != b
        case _ => false
      }, simplify(p1)) match {
        case Some((PEq(v@Var(x), e), rest1)) =>
          val _p1 = mkConjunction(rest1).subst(v, e)
          val _s1 = s1.subst(v, e)
          val _p2 = p2.subst(v, e)
          val _s2 = s2.subst(v, e)
          val newSpec = Spec(
            Assertion(_p1, _s1),
            Assertion(_p2, _s2),
            g.filter { case (t, w) => w != v })
          EntMoreGoals(List(newSpec))
        case _ => EntFail
      }
    }
  }

  // [Inconsistency]
  object Inconsistency extends EntailmentRule {
    override def toString: String = "[Norm: Inconsistency]"

    def apply(spec: Spec, env: Environment): EntRuleResult = {
      val Spec(Assertion(p1, s1), Assertion(p2, s2), g) = spec
      val res = findConjunctAndRest({
        case PNeg(PEq(x, y)) => x == y
        case _ => false
      }, simplify(p1))
      res match {
        case Some((PNeg(PEq(x, y)), rest1)) if x == y =>
          EntMoreGoals(Nil)
        case _ => EntFail
      }
    }
  }

  // [=-L]
  object StripEqPre extends EntailmentRule {
    override def toString: String = "[Norm: =-L]"

    def apply(spec: Spec, env: Environment): EntRuleResult = {
      findConjunctAndRest({
        case PEq(x, y) => x == y
        case _ => false
      }, simplify(spec.pre.phi)) match {
        case None => EntFail
        case Some((_, rest)) =>
          val newPre = Assertion(mkConjunction(rest), spec.pre.sigma)
          val newSpec = Spec(newPre, spec.post, spec.gamma)
          EntMoreGoals(List(newSpec))
      }
    }
  }

  // TODO: implement *-Partial

  /* *********************************************************
   * SUBTRACTION RULES
   * *********************************************************/

  // [AXIOM]
  object Axiom extends EntailmentRule {
    override def toString: String = "[Sub: Axiom]"
    def apply(spec: Spec, env: Environment): EntRuleResult = {
      val p = simplify(spec.post.phi)
      val s1 = spec.pre.sigma
      val s2 = spec.post.sigma
      if (p == PTrue && s1.isEmp && s2.isEmp) EntMoreGoals(Nil) else EntFail
    }
  }

  //[=-R]
  object StripEqPost extends EntailmentRule {
    override def toString: String = "[Sub: =-R]"

    def apply(spec: Spec, env: Environment): EntRuleResult = {
      findConjunctAndRest({
        case PEq(x, y) => x == y
        case _ => false
      }, simplify(spec.post.phi)) match {
        case None => EntFail
        case Some((_, rest)) =>
          val newPost = Assertion(mkConjunction(rest), spec.post.sigma)
          val newSpec = Spec(spec.pre, newPost, spec.gamma)
          EntMoreGoals(List(newSpec))
      }
    }
  }

  // [HYPOTHESIS]
  object Hypothesis extends EntailmentRule {
    override def toString: String = "[Sub: Hypothesis]"
    def apply(spec: Spec, env: Environment): EntRuleResult = {
      (conjuncts(spec.pre.phi), conjuncts(spec.post.phi)) match {
        case (Some(cs1), Some(cs2)) =>
          findCommon((p: PFormula) => true, cs1, cs2) match {
            case Some((p, ps1, ps2)) =>
              val newPost = Assertion(mkConjunction(ps2), spec.post.sigma)
              val newSpec = Spec(spec.pre, newPost, spec.gamma)
              EntMoreGoals(List(newSpec))
            case None => EntFail
          }
        case _ => EntFail
      }
    }
  }

  // [*-INTRODUCTION]
  object StarIntro extends EntailmentRule {
    override def toString: String = "[Sub: *-Introduction]"
    def apply(spec: Spec, env: Environment): EntRuleResult = {
      val cs1 = spec.pre.sigma.chunks
      val cs2 = spec.pre.sigma.chunks
      findCommon((h: Heaplet) => h.isInstanceOf[PointsTo], cs1, cs2) match {
        case Some((p, ps1, ps2)) =>
          val newPre = Assertion(spec.pre.phi, SFormula(ps1))
          val newPost = Assertion(spec.post.phi, SFormula(ps2))
          val newSpec = Spec(newPre, newPost, spec.gamma)
          EntMoreGoals(List(newSpec))
        case None => EntFail
      }
    }
  }

}

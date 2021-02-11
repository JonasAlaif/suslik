package org.tygus.suslik.certification.targets.htt.logic

import org.tygus.suslik.certification.targets.htt.language.Expressions._
import org.tygus.suslik.certification.targets.htt.language.{CFormals, CGamma, PrettyPrinting}
import org.tygus.suslik.certification.targets.htt.language.Types._
import org.tygus.suslik.certification.targets.htt.translation.IR.CSubst

object Sentences {
  case class CAssertion(phi: CExpr, sigma: CSFormula) extends PrettyPrinting {
    override def pp: String = if (phi.isTrivial) sigma.pp else s"${phi.pp} /\\ ${sigma.pp}"

    def existentials(quantifiedVars: Seq[CVar]): Seq[CVar] = valueVars.diff(quantifiedVars)

    def ppQuantified(quantifiedVars: Seq[CVar], depth: Int = 0, gamma: CGamma = Map.empty): String = {
      val builder = new StringBuilder()

      val valueEx = existentials(quantifiedVars)
      val heapEx = heapVars
      if (valueEx.nonEmpty) {
        builder.append(s"exists ${valueEx.map(v => gamma.get(v).map(t => s"(${v.pp} : ${t.pp})").getOrElse(v.pp)).mkString(" ")},\n")
      }
      if (heapEx.nonEmpty) {
        builder.append(s"exists ${heapEx.map(_.pp).mkString(" ")},\n")
      }

      builder.append(pp)

      getIndent(depth) + builder.toString().replaceAll("\n", s"\n${getIndent(depth)}")
    }

    def subst(sub: CSubst): CAssertion =
      CAssertion(phi.subst(sub), sigma.subst(sub))

    val valueVars: Seq[CVar] =
      (phi.vars ++ sigma.vars).distinct.diff(phi.cardVars ++ sigma.cardVars)

    val heapVars: Seq[CVar] =
      sigma.heapVars

    def removeCardConstraints: CAssertion = {
      val cardVars = sigma.cardVars
      val conjuncts = phi.conjuncts.filter {
        case CBinaryExpr(_, v:CVar, _) if cardVars.contains(v) => false
        case CBinaryExpr(_, _, v:CVar) if cardVars.contains(v) => false
        case _ => true
      }
      val phi1 = if (conjuncts.isEmpty) CBoolConst(true) else conjuncts.reduce[CExpr] { case (c1, c2) => CBinaryExpr(COpAnd, c1, c2) }
      this.copy(phi = phi1)
    }
  }

  case class CInductiveClause(pred: String, idx: Int, selector: CExpr, asn: CAssertion, existentials: Seq[CExpr]) extends PrettyPrinting {
    def subst(sub: CSubst): CInductiveClause =
      CInductiveClause(pred, idx, selector.subst(sub), asn.subst(sub), existentials.map(_.subst(sub)))
  }

  case class CInductivePredicate(name: String, params: CFormals, clauses: Seq[CInductiveClause], gamma: CGamma) extends PrettyPrinting {
    val paramVars: Seq[CVar] = params.map(_._1)

    def subst(sub: CSubst): CInductivePredicate =
      CInductivePredicate(
        name,
        params.map(p => (p._1.substVar(sub), p._2)),
        clauses.map(_.subst(sub)),
        gamma.map(g => (g._1.substVar(sub), g._2))
      )

    override def pp: String = {
      val builder = new StringBuilder()
      builder.append(s"Inductive $name ${params.map{ case (v, t) => s"(${v.pp} : ${t.pp})" }.mkString(" ")} : Prop :=\n")

      // clauses
      val clausesStr = for {
        CInductiveClause(pred, idx, selector, asn, _) <- clauses
      } yield s"| ${pred}_$idx of ${selector.pp} of\n${asn.ppQuantified(paramVars, 1, gamma)}"

      builder.append(s"${clausesStr.mkString("\n")}.\n")
      builder.toString()
    }
  }

  case class CFunSpec(name: String, rType: HTTType, params: CFormals, ghostParams: CFormals, pre: CAssertion, post: CAssertion) extends PrettyPrinting {
    val paramVars: Seq[CVar] = params.map(_._1)
    val ghostParamVars: Seq[CVar] = ghostParams.map(_._1)

    val progVarsAlias = "vprogs"
    val ghostVarsAlias = "vghosts"

    val existentials: Seq[CVar] = post.valueVars.diff(paramVars ++ ghostParamVars)

    def subst(subst: CSubst): CFunSpec =
      CFunSpec(name, rType, params.map(p => (p._1.substVar(subst), p._2)), ghostParams.map(p => (p._1.substVar(subst), p._2)), pre.subst(subst), post.subst(subst))

    private def ppFormals(formals: CFormals): (String, String) = {
      val (names, typs) = formals.unzip
      val typsStr = typs.map(_.pp).mkString(" * ")
      val namesStr = names.map(_.pp).mkString(", ")
      (typsStr, namesStr)
    }

    override def pp: String = {
      val builder = new StringBuilder()

      val (progVarsStr, typsStr) = ppFormals(params)
      val (ghostVarsStr, ghostTypsStr) = ppFormals(ghostParams)
      val destructuredAliases = {
        val destructuredParams = if (params.nonEmpty) s"${getIndent(3)}let: ($progVarsStr) := $progVarsAlias in\n" else ""
        val destructuredGhostParams = if (ghostParams.nonEmpty) s"${getIndent(3)}let: ($ghostVarsStr) := $ghostVarsAlias in\n" else ""
        destructuredParams + destructuredGhostParams
      }

      builder.append(s"Definition ${name}_type :=\n")

      // program var signatures
      if (params.nonEmpty) {
        builder.append(s"${getIndent(1)}forall ($progVarsAlias : $typsStr),\n")
      }

      // ghost var signatures
      if (ghostParams.nonEmpty) {
        builder.append(s"${getIndent(1)}{($ghostVarsAlias : $ghostTypsStr)},\n")
      }

      builder.append(s"${getIndent(1)}STsep (\n")

      // pre-condition
      builder.append(s"${getIndent(2)}fun h =>\n")
      builder.append(destructuredAliases)
      builder.append(pre.ppQuantified(paramVars ++ ghostParamVars, 3))
      builder.append(",\n")

      // post-condition
      builder.append(s"${getIndent(2)}[vfun (_: ${rType.pp}) h =>\n")
      builder.append(destructuredAliases)
      builder.append(post.ppQuantified(paramVars ++ ghostParamVars, 3))
      builder.append("\n")

      builder.append(s"${getIndent(2)}]).")

      builder.toString()
    }
  }
}

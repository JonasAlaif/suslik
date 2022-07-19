package org.tygus.suslik.language

import org.tygus.suslik.logic.Specifications.GoalLabel
import org.tygus.suslik.logic.{Formals, FunSpec, Gamma}
import org.tygus.suslik.util.StringUtil._
import org.tygus.suslik.logic.InductivePredicate

/**
  * @author Ilya Sergey
  */
object Statements {

  import Expressions._

  sealed abstract class Statement extends HasExpressions[Statement] {

    // Pretty-printer
    def pp(rets: List[Var] = Nil): String = {

      val builder = new StringBuilder

      def doRet(offset: Int, sub: Subst, rets: List[Var]) = {
        if (rets.length > 0) {
          val retsStr = rets.map(r => sub.getOrElse(r, r).pp)
          val retStr = if (retsStr.length == 1) retsStr(0) else retsStr.mkString("(", ", ", ")")
          builder.append("\n" + mkSpaces(offset)).append(retStr)
        }
      }

      def build(s: Statement, offset: Int = 2, sub: Subst = Map(), rets: List[Var]): (Subst, Boolean) = {
        s.simplify match {
          case Skip => (sub, true)
          case Hole =>
            builder.append(mkSpaces(offset))
            builder.append(s"??")
            (sub, true)
          case Error =>
            builder.append(mkSpaces(offset))
            builder.append(s"unreachable!()")
            (sub, false)
          case Sub(s) =>
            // builder.append(mkSpaces(offset))
            // builder.append(s"// subst(${s.map(m => s"${m._1.pp} -> ${m._2.pp}").mkString(", ")})\n")
            var newSub = sub.mapValues(v => v.subst(s)) ++ s
            var changed = true
            while (changed) {
              val updateSub = newSub.mapValues(v => v.subst(newSub))
              changed = newSub != updateSub
              newSub = updateSub
            }
            // builder.append(s"// [${newSub.map(m => s"${m._1.pp} -> ${m._2.pp}").mkString(", ")}]\n\n")
            (newSub, true)
          case Malloc(to, _, sz) =>
            // Ignore type
            builder.append(mkSpaces(offset))
            builder.append(s"let ${to.pp} = malloc($sz);")
            (sub, true)
          case Free(v) =>
            builder.append(mkSpaces(offset))
            builder.append(s"free(${v.pp});")
            (sub, true)
          case Store(to, off, e) =>
            val (toSub, eSub) = (UnaryExpr(OpDeRef, to.subst(sub)).normalise, e.subst(sub))
            builder.append(mkSpaces(offset))
            assert(off == 0)
            builder.append(s"${toSub.pp} = ${eSub.pp};")
            (sub, true)
          case Load(to, _, from, off) =>
            builder.append(mkSpaces(offset))
            val f = if (off <= 0) from.pp else s"(${from.pp} + $off)"
            // Do not print the type annotation
            builder.append(s"let ${to.pp} = *$f;")
            (sub, true)
          case c@Construct(_, _, _, _) =>
            val Construct(to, pred, variant, args) = c.subst(sub)
            builder.append(mkSpaces(offset))
            val structLike = args.exists(arg => arg.isInstanceOf[BinaryExpr] && arg.asInstanceOf[BinaryExpr].op == OpFieldBind)
            val cName = variant.getOrElse(pred)
            val bra = if (args.length == 0) "" else if (structLike) " { " else "("
            val ket = if (args.length == 0) "" else if (structLike) " }" else ")"
            val isRes = rets.length == 1 && sub.getOrElse(rets(0), rets(0)) == to
            builder.append(s"${if (isRes) "" else s"let ${to.pp} = "}$cName$bra${args.map(_.pp).mkString(", ")}$ket${if (isRes) "" else ";"}")
            (sub, !isRes)
          case m@Match(tgt, arms) =>
            val tSub = tgt.subst(sub)
            builder.append(mkSpaces(offset)).append(s"match ${tSub.pp} {\n")
            arms.map { case (constr, stmt) =>
              val (_, ret) = build(constr, offset + 2, sub, List(Var("result")))
              assert(!ret)
              builder.append(" =>")
              if (stmt.size > 0 || rets.length == 0) builder.append(if (stmt.size == 0) " {" else " {\n")
              val (resSub, mustRet) = build(stmt, offset + 4, sub, rets)
              if (mustRet) doRet(offset + 4, resSub, rets)
              if (stmt.size > 0 || rets.length == 0) builder.append(if (stmt.size == 0) "}\n" else ("\n" + mkSpaces(offset + 2) + "}\n"))
              else builder.append(",\n")
            }
            builder.append(mkSpaces(offset)).append(s"}")
            (sub, false)
          case c@Call(_, _, _, _) =>
            val Call(fun, result, args, _) = c.subst(sub)
            builder.append(mkSpaces(offset))
            val isRes = rets.length > 0 && rets.length == result.length &&
              rets.zip(result).forall(ret => sub.getOrElse(ret._1, ret._1) == ret._2)
            val res = if (isRes) ""
              else if (result.length == 0) ""
              else if (result.length == 1) s"let ${result.head.pp} = "
              else "let (" + result.map(_.pp).mkString(", ") + ") = "
            val function_call = s"$res${fun.pp}(${args.map(_.pp).mkString(", ")})${if (isRes) "" else ";"}"
            builder.append(function_call)
            (sub, !isRes)
          case SeqComp(s1,s2) =>
            val (nSub, mustRet) = build(s1, offset, sub, if (s2.size > 0) Var("-unretable-") :: rets else rets)
            if (s2.size > 0 && !mustRet) {
              println("Trying to return at:\n" + builder.toString())
              println("While still have:\n" + s2.pp())
              assert(false)
            }
            if (s1.size > 0 && s2.size > 0) builder.append(s"\n")
            build(s2, offset, nSub, rets)
          case If(cond, tb, eb) =>
            builder.append(mkSpaces(offset))
            builder.append(s"if (${cond.subst(sub).pp}) {")
            if (tb.size > 0) builder.append(s"\n")
            val (resT, mustRetT) = build(tb, offset + 2, sub, rets)
            // Result true:
            if (mustRetT) doRet(offset+2, resT, rets)
            builder.append("\n" + mkSpaces(offset)).append(s"} else {")
            if (eb.size > 0) builder.append(s"\n")
            val (resF, mustRetF) = build(eb, offset + 2, sub, rets)
            // Result false:
            if (mustRetF) doRet(offset+2, resF, rets)
            builder.append("\n" + mkSpaces(offset)).append(s"}")
            (sub, false)
          case Guarded(cond, b) =>
            builder.append(mkSpaces(offset))
            builder.append(s"assume (${cond.pp}) {\n")
            build(b, offset + 2, sub, rets)
            builder.append("\n" + mkSpaces(offset)).append(s"}")
            (sub, true)
        }
      }

      val (res, mustRet) = build(this, rets = rets)
      if (mustRet) doRet(2, res, rets)
      builder.toString()
    }

    // Expression-collector
    def collect[R <: Expr](p: Expr => Boolean): Set[R] = {

      def collector(acc: Set[R])(st: Statement): Set[R] = st match {
        case Skip => acc
        case Hole => acc
        case Error => acc
        case Sub(s) => acc ++ s.values.flatMap(_.collect(p))
        case Store(to, off, e) =>
          acc ++ to.collect(p) ++ e.collect(p)
        case Load(_, _, from, off) =>
          acc ++ from.collect(p)
        case Construct(to, _, _, args) =>
          acc ++ to.collect(p) ++ args.flatMap(_.collect(p)).toSet
        case Match(tgt, arms) =>
          acc ++ tgt.collect(p) ++ arms.flatMap(a => a._1.collect(p) ++ a._2.collect(p))
        case Malloc(_, _, _) =>
          acc
        case Free(x) =>
          acc ++ x.collect(p)
        case Call(fun, res, args, _) =>
          acc ++ fun.collect(p) ++ res.flatMap(_.collect(p)).toSet ++ args.flatMap(_.collect(p)).toSet
        case SeqComp(s1,s2) =>
          val acc1 = collector(acc)(s1)
          collector(acc1)(s2)
        case If(cond, tb, eb) =>
          val acc1 = collector(acc ++ cond.collect(p))(tb)
          collector(acc1)(eb)
        case Guarded(cond, b) =>
          collector(acc ++ cond.collect(p))(b)
      }

      collector(Set.empty)(this)
    }

    override def subst(sigma: Subst): Statement = this match {
      case Store(to, off, e) => {
        assert(!sigma.keySet.contains(to) || sigma(to).isInstanceOf[Var])
        Store(to.subst(sigma).asInstanceOf[Var], off, e.subst(sigma))
      }
      case Load(to, tpe, from, offset) => {
        assert(!sigma.keySet.contains(to) || sigma(to).isInstanceOf[Var])
        assert(!sigma.keySet.contains(from) || sigma(from).isInstanceOf[Var])
        Load(to.subst(sigma).asInstanceOf[Var], tpe, from.subst(sigma).asInstanceOf[Var], offset)
      }
      case Construct(to, pred, variant, args) =>
        assert(!sigma.keySet.contains(to) || sigma(to).isInstanceOf[Var])
        Construct(to.subst(sigma).asInstanceOf[Var], pred, variant, args.map(_.subst(sigma)))
      case Match(tgt, arms) =>
        Match(tgt.subst(sigma), arms.map(a => (a._1, a._2.subst(sigma))))
      case Malloc(to, tpe, sz) => {
        assert(!sigma.keySet.contains(to) || sigma(to).isInstanceOf[Var])
        Malloc(to.subst(sigma).asInstanceOf[Var], tpe, sz)
      }
      case Free(x) => {
        assert(!sigma.keySet.contains(x) || sigma(x).isInstanceOf[Var])
        Free(x.subst(sigma).asInstanceOf[Var])
      }
      case Call(fun, res, args, companion) => Call(fun, res.map(_.subst(sigma).asInstanceOf[Var]), args.map(_.subst(sigma)), companion)
      case SeqComp(s1, s2) => SeqComp(s1.subst(sigma), s2.subst(sigma))
      case If(cond, tb, eb) => If(cond.subst(sigma), tb.subst(sigma), eb.subst(sigma))
      case Guarded(cond, b) => Guarded(cond.subst(sigma), b.subst(sigma))
      case _ => this
    }

    // Statement size in AST nodes
    def size: Int = this match {
      case Skip => 0
      case Hole => 1
      case Error => 1
      case Sub(_) => 0
      case Store(to, off, e) => 1 + to.size + e.size
      case Load(to, _, from, _) => 1 + to.size + from.size
      case Construct(to, _, _, args) => 1 + to.size + args.map(_.size).sum
      case Match(_, arms) => 1 + arms.map(a => a._1.size + a._2.size).sum
      case Malloc(to, _, _) => 1 + to.size
      case Free(x) => 1 + x.size
      case Call(_, res, args, _) => 1 + res.size + args.map(_.size).sum
      case SeqComp(s1,s2) => s1.size + s2.size
      case If(cond, tb, eb) => 1 + cond.size + tb.size + eb.size
      case Guarded(cond, b) => 1 + cond.size + b.size
    }

    // Simplified statement: by default do nothing
    def simplify: Statement = this

    // Is this an atomic statement?
    def isAtomic: Boolean = this match {
      case Skip => false
      case If(_,_,_) => false
      case Match(_,_) => false
      case Guarded(_,_) => false
      case SeqComp(_,_) => false
      case _ => true
    }

    // Variables defined by this atomic statement
    def definedVars: Set[Var] = this match {
      case Load(y, _, _, _) => Set(y)
      case Malloc(y, _, _)  => Set (y)
      case _ if !isAtomic => {assert(false, "definedVars called on non-atomic statement"); Set()}
      case _ => Set()
    }

    // All atomic statements (load, store, malloc, free, call) inside this statement
    def atomicStatements: List[Statement] = this match {
      case Skip => List()
      case SeqComp(s1,s2) => s1.atomicStatements ++ s2.atomicStatements
      case If(_, tb, eb) => tb.atomicStatements ++ eb.atomicStatements
      case Match(_, arms) => arms.flatMap(_._2.atomicStatements).toList
      case Guarded(_, b) => b.atomicStatements
      case _ => List(this)
    }

    // Apply f to all atomic statements inside this statement
    def mapAtomic(f: Statement => Statement): Statement = this match {
      case SeqComp(s1, s2) => SeqComp(s1.mapAtomic(f), s2.mapAtomic(f))
      case If(cond, tb, eb) => If(cond, tb.mapAtomic(f), eb.mapAtomic(f))
      case Match(tgt, arms) => Match(tgt, arms.map(a => (a._1, a._2.mapAtomic(f))))
      case Guarded(cond, b) => Guarded(cond, b.mapAtomic(f))
      case Skip => Skip
      case _ => f(this)
    }

    // Companions of all calls inside this statement
    def companions: List[GoalLabel] = atomicStatements.flatMap {
      case Call(_, _, _, Some(comp)) => List(comp)
      case _ => Nil
    }

    def uncons: (Statement, Statement) = this match {
      case SeqComp(s1, s2) => {
        val (head, tail) = s1.uncons
        tail match {
          case Skip => (head, s2)
          case _ => (head, SeqComp(tail, s2))
        }
      }
      case other => (other, Skip)
    }

    def resolveOverloading(gamma: Gamma): Statement = this match {
      case SeqComp(s1,s2)=> SeqComp(
        s1.resolveOverloading(gamma),
        s2.resolveOverloading(gamma)
      )
      case If(cond, tb, eb) => If(
        cond.resolveOverloading(gamma),
        tb.resolveOverloading(gamma),
        eb.resolveOverloading(gamma)
      )
      case Match(tgt, arms) => Match(
        tgt.resolveOverloading(gamma),
        arms.map(a => (a._1, a._2.resolveOverloading(gamma)))
      )
      case Guarded(cond, body) => Guarded(
        cond.resolveOverloading(gamma),
        body.resolveOverloading(gamma)
      )
      case cmd:Store => cmd.copy(e = cmd.e.resolveOverloading(gamma))
      case cmd:Call => cmd.copy(args = cmd.args.map({e => e.resolveOverloading(gamma)}))
      case other => other
    }

    // Shorten a variable v to its minimal prefix unused in the current statement.
    def simplifyVariable(v: Var): (Var, Statement) = (v, this)
    // {
    //   val used = this.vars
    //   val prefixes = Range(1, v.name.length).map(n => v.name.take(n))
    //   prefixes.find(p => !used.contains(Var(p))) match {
    //     case None => (v, this) // All shorter names are taken
    //     case Some(name) => (Var(name), this.subst(v, Var(name)))
    //   }
    // }
  }

  // skip
  case object Skip extends Statement

  // ??
  case object Hole extends Statement

  // assert false
  case object Error extends Statement

  // substitute in past goals
  case class Sub(sub: Subst) extends Statement

  // let to = malloc(n)
  case class Malloc(to: Var, tpe: SSLType, sz: Int = 1) extends Statement

  // free(v)
  case class Free(v: Var) extends Statement

  // let to = *from.offset
  case class Load(to: Var, tpe: SSLType, from: Var,
                  offset: Int = 0) extends Statement

  // let to = pred(args)
  case class Construct(to: Var, pred: Ident, variant: Option[String], args: Seq[Expr]) extends Statement

  // match tgt { arms }
  case class Match(tgt: Expr, arms: Seq[(Construct, Statement)]) extends Statement

  // *to.offset = e
  case class Store(to: Var, offset: Int, e: Expr) extends Statement

  // f(args)
  case class Call(fun: Var, result: List[Var], args: Seq[Expr], companion: Option[GoalLabel]) extends Statement

  // s1; s2
  case class SeqComp(s1: Statement, s2: Statement) extends Statement {
    override def simplify: Statement = {
      (s1, s2) match {
        case (Skip, _) => s2.simplify // Remove compositions with skip
        case (Error, _) => Error
//        case (_, Skip) => s1.simplify
        case (SeqComp(s11, s12), _) => SeqComp(s11, SeqComp(s12, s2)).simplify // Left-nested compositions are transformed to right-nested
        case (If(g, t, f), _) => If(g, SeqComp(t, s2).simplify, SeqComp(f, s2).simplify)
        case (Match(tgt, arms), _) => Match(tgt, arms.map(a => (a._1, SeqComp(a._2, s2).simplify)))
        case (_, Guarded(cond, b)) // Guards are propagated to the top but not beyond the definition of any var in their cond
            if cond.vars.intersect(s1.definedVars).isEmpty => Guarded(cond, SeqComp(s1, b).simplify)
        case (Load(y, tpe, from, offset), _) => simplifyBinding(y, newY => Load(newY, tpe, from, offset))
        case (Malloc(to, tpe, sz), _) => simplifyBinding(to, newTo => Malloc(newTo, tpe, sz))
        case _ => this
      }
    }

    // Eliminate or shorten newly bound variable newvar
    // depending on the rest of the program (s2)
    private def simplifyBinding(newvar: Var, mkBinding: Var => Statement): Statement =
      if (s2.vars.contains(newvar)) {
        val (v, s) = s2.simplifyVariable(newvar)
        SeqComp(mkBinding(v), s)
      } else s2  // Do not generate bindings for unused variables
  }

  // if (cond) { tb } else { eb }
  case class If(cond: Expr, tb: Statement, eb: Statement) extends Statement {
    override def simplify: Statement = {
      (tb, eb) match {
        case (Skip, Skip) => Skip
        // case (Error, _) => eb
        // case (_, Error) => tb
        case (Guarded(gcond, gb), _) => Guarded(gcond, If(cond, gb, eb).simplify)
        case (_, Guarded(gcond, gb)) => Guarded(gcond, If(cond, tb, gb).simplify)
        case _ => this
      }
    }
  }

  // assume cond { body } else { els }
  case class Guarded(cond: Expr, body: Statement) extends Statement {
    override def simplify: Statement = body match {
      case Guarded(c1, b1) => Guarded(cond && c1, b1)
      case _ => this
    }
  }

  // A procedure
  case class Procedure(f: FunSpec, body: Statement)(implicit predicates: Map[Ident, InductivePredicate]) {
    
    val (name: String, tp: SSLType, formals: Formals) = (f.name, f.rType, f.params)

    def pp: String = {
      val generics = if (f.lfts.size == 0) "" else s"<${f.lfts.mkString(", ")}>"
      val returns =
        if (f.rustReturns.length == 0) ""
        else if (f.rustReturns.length == 1) s"-> ${f.rustReturns.head._2.map(_.sig).mkString("")}${f.rustReturns.head._3} "
        else s"-> (${f.rustReturns.map(r => r._2.map(_.sig).mkString("") + r._3).mkString(", ")}) "
      s"""
          |fn $name$generics(${f.rustParams.map { case (f, r, t) => s"${f.pp}: ${r.map(_.sig).mkString("")}$t" }.mkString(", ")}) $returns{
          |${body.pp(f.result)}
          |}
      """.stripMargin
    }

    // def ppOld: String =
    //   s"""
    //      |${tp.pp} $name (${formals.map { case (i, t) => s"${t.pp} ${i.pp}" }.mkString(", ")}) {
    //      |${body.pp(f.result)}
    //      |}
    // """.stripMargin

    // Shorten parameter names
    def simplifyParams: Procedure = {
      // TODO: enable simplification
      return this
      type Acc = (FunSpec, Statement)
      def updateParam(formal: (Var, SSLType), acc: Acc): Acc = {
        val (newParam, newBody) = acc._2.simplifyVariable(formal._1)
        val newSpec = acc._1.varSubst(Map(formal._1 -> newParam))
        (newSpec, newBody)
      }
      val (newSpec, newBody) = f.params.foldRight((f, body))(updateParam)
      this.copy(f = newSpec, body = newBody)
    }

    // Removed unused formals from this procedure
    // and corresponding actuals in all recursive calls;
    // a parameter is considered unused if it is only mentioned in a recursive call
    // at the same (or other unused) position
    def removeUnusedParams(outerCall: Call): (Procedure, Call) = {

      def isRecCall(s: Statement) = s.isInstanceOf[Call] && s.asInstanceOf[Call].fun.name == f.name
      val recCalls = body.atomicStatements.filter(isRecCall).map(_.asInstanceOf[Call])
      val rest = body.mapAtomic(s => if (isRecCall(s)) Skip else s)

      def rmAtIndex(args: Seq[Expr], i: Int): Seq[Expr] = args.take(i) ++ args.drop(i + 1)

      val unusedParams = for {
        param <- f.params
        if !rest.vars.contains(param._1)
        ind = f.params.indexOf(param)
        if recCalls.forall(c => !rmAtIndex(c.args, ind).flatMap(_.vars).contains(param._1))
      } yield (ind, param)

      val unusedArgs = unusedParams.map(_._1)
      def removeUnusedArgs(c:Call): Call = {
        val newArgs = c.args.indices.filterNot(unusedArgs.contains(_)).map(i => c.args(i))
        c.copy(args = newArgs)
      }
      def removeCallArgs(s: Statement): Statement = if (isRecCall(s)) {
        removeUnusedArgs(s.asInstanceOf[Call])
      } else s

      val usedParams = f.params.filterNot(p => unusedParams.map(_._2).contains(p))
      val newProc = this.copy(f = this.f.copy(params = usedParams), body = this.body.mapAtomic(removeCallArgs))
      val newCall = removeUnusedArgs(outerCall)
      (newProc, newCall)
    }

  }

  // Solution for a synthesis goal:
  // a statement and a possibly empty list of recursive helpers
  type Solution = (Statement, List[Procedure])

}

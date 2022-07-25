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

      def doRet(rets: List[Expr]): String = {
        if (rets.length > 0)
          if (rets.length == 1) rets(0).pp
          else rets.map(_.pp).mkString("(", ", ", ")")
        else "()"
      }
      def toRet(s: Statement, rets: List[Var]): Statement =
        SeqComp(s, Call(Var("return "), List.empty, rets, None)).simplify.toPP

      def build(s: Statement, offset: Int = 2): Unit = {
        assert(s.simplify == s, "Simp: " + s.simplify + " vs " + s)
        s match {
          case Skip => ()
          case Hole =>
            builder.append("??")
          case Error =>
            builder.append("unreachable!()")
          case Sub(subst) =>
            // assert(false, "Encountered unexpected substitution " + subst)
            // // builder.append(mkSpaces(offset))
            builder.append(s"// subst(${subst.map(m => s"${m._1.pp} -> ${m._2.pp}").mkString(", ")})\n")
            // var newSub = sub.mapValues(v => v.subst(s)) ++ s
            // var changed = true
            // while (changed) {
            //   val updateSub = newSub.mapValues(v => v.subst(newSub))
            //   changed = newSub != updateSub
            //   newSub = updateSub
            // }
            // // builder.append(s"// [${newSub.map(m => s"${m._1.pp} -> ${m._2.pp}").mkString(", ")}]\n\n")
            // (newSub, true)
          case Malloc(to, _, sz) =>
            // Ignore type
            builder.append(s"let ${to.pp} = malloc($sz);")
          case Free(v) =>
            builder.append(s"free(${v.pp});")
          case s@Store(to, off, e) =>
            builder.append(s"${UnaryExpr(OpDeRef, to).normalise.pp} = ${e.pp}${if (s.isRes) "" else ";"}")
          case Load(to, _, from, off) =>
            val f = if (off <= 0) from.pp else s"(${from.pp} + $off)"
            // Do not print the type annotation
            builder.append(s"let ${to.pp} = *$f;")
          case c@Construct(to, pred, variant, args) =>
            val structLike = args.exists(arg => arg.isInstanceOf[BinaryExpr] && arg.asInstanceOf[BinaryExpr].op == OpFieldBind)
            val bra = if (args.length == 0) "" else if (structLike) " { " else "("
            val ket = if (args.length == 0) "" else if (structLike) " }" else ")"
            builder.append(s"${if (c.isRes) "" else s"let ${to.pp} = "}${c.cName}$bra${args.map(_.pp).mkString(", ")}$ket${if (c.isRes) "" else ";"}")
          case m@Match(res, tgt, arms) =>
            val trueRes = if (m.isRes) res.tail else res
            val resStr = if (m.isRes || trueRes.length == 0) "" else s"let ${doRet(trueRes)} = "
            builder.append(resStr).append(s"match ${tgt.pp} {\n")
            arms.map { case (constr, stmt) =>
              builder.append(mkSpaces(offset+2))
              build(constr, 0)
              builder.append(" => ")
              val fullStmt = toRet(stmt, trueRes)
              if (!fullStmt.isRes) builder.append("{\n" + mkSpaces(offset+4))
              build(fullStmt, offset + 4)
              if (!fullStmt.isRes) builder.append("\n" + mkSpaces(offset+2) + "}\n")
              else builder.append(",\n")
            }
            builder.append(mkSpaces(offset)).append(if (m.isRes) "}" else "};")
          case Call(fun, _, args, _) if fun.name == "return " =>
            builder.append(doRet(args.toList))
          case c@Call(fun, result, args, _) =>
            val res = if (c.isRes || result.length == 0) ""
              else s"let ${doRet(result)} = "
            val function_call = s"$res${fun.pp}(${args.map(_.pp).mkString(", ")})${if (c.isRes) "" else ";"}"
            builder.append(function_call)
          case SeqComp(s1,s2) =>
            build(s1, offset)
            builder.append("\n" + mkSpaces(offset))
            build(s2, offset)
          case i@If(rets, _, _, _) =>
            val trueRets = if (i.isRes) rets.tail else rets
            if (trueRets.length > 0 && !i.isRes) builder.append(s"let ${doRet(trueRets)} = ")
            var ecase: Statement = i
            while (ecase match {
              case If(orets, cond, tb, eb) if orets.toSet == rets.toSet =>
                val tbRet = toRet(tb, trueRets)
                builder.append(s"if ${cond.pp} {")
                builder.append(if (!tbRet.isRes) "\n" + mkSpaces(offset+2) else " ")
                build(tbRet, offset + 2)
                builder.append(if (!tbRet.isRes) "\n" + mkSpaces(offset) else " ")
                builder.append("}")
                ecase = toRet(eb, trueRets)
                if (ecase.size > 0) {
                  builder.append(" else ")
                  true
                } else false
              case _ => false
            }) {}
            if (ecase.size > 0) {
              builder.append("{")
              builder.append(if (!ecase.isRes) "\n" + mkSpaces(offset+2) else " ")
              build(ecase, offset + 2)
              builder.append(if (!ecase.isRes) "\n" + mkSpaces(offset) else " ")
              builder.append(if (i.isRes) "}" else "};")
            }
          case Guarded(cond, b) =>
            builder.append(s"assume (${cond.pp}) {\n")
            build(b, offset + 2)
            builder.append("\n" + mkSpaces(offset)).append(s"}")
        }
      }
      build(toRet(this, rets))
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
        case Match(r, tgt, arms) =>
          acc ++ r.flatMap(_.collect(p)) ++ tgt.collect(p) ++ arms.flatMap(a => a._1.collect(p) ++ a._2.collect(p))
        case Malloc(_, _, _) =>
          acc
        case Free(x) =>
          acc ++ x.collect(p)
        case Call(fun, res, args, _) =>
          acc ++ fun.collect(p) ++ res.flatMap(_.collect(p)).toSet ++ args.flatMap(_.collect(p)).toSet
        case SeqComp(s1,s2) =>
          val acc1 = collector(acc)(s1)
          collector(acc1)(s2)
        case If(r, cond, tb, eb) =>
          val acc1 = collector(acc  ++ r.flatMap(_.collect(p)) ++ cond.collect(p))(tb)
          collector(acc1)(eb)
        case Guarded(cond, b) =>
          collector(acc ++ cond.collect(p))(b)
      }

      collector(Set.empty)(this)
    }

    override def subst(sigma: Subst): Statement = this match {
      case Store(to, off, e) => {
        Store(to.subst(sigma), off, e.subst(sigma))
      }
      case Load(to, tpe, from, offset) => {
        assert(!sigma.keySet.contains(to) || sigma(to).isInstanceOf[Var])
        assert(!sigma.keySet.contains(from) || sigma(from).isInstanceOf[Var])
        Load(to.subst(sigma).asInstanceOf[Var], tpe, from.subst(sigma).asInstanceOf[Var], offset)
      }
      case Sub(subst) => ???
      case Construct(to, pred, variant, args) =>
        assert(!sigma.keySet.contains(to) || sigma(to).isInstanceOf[Var])
        Construct(to.subst(sigma).asInstanceOf[Var], pred, variant, args.map(_.subst(sigma)))
      case Match(r, tgt, arms) =>
        Match(r, tgt.subst(sigma), arms.map(a => (a._1, SeqComp(Sub(sigma), a._2))))
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
      case If(r, cond, tb, eb) => If(r, cond.subst(sigma), SeqComp(Sub(sigma), tb), SeqComp(Sub(sigma), eb))
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
      case Match(_, _, arms) => 1 + arms.map(a => a._1.size + a._2.size).sum
      case Malloc(to, _, _) => 1 + to.size
      case Free(x) => 1 + x.size
      case Call(_, res, args, _) => 1 + res.size + args.map(_.size).sum
      case SeqComp(s1,s2) => s1.size + s2.size
      case If(_, cond, tb, eb) => 1 + cond.size + tb.size + eb.size
      case Guarded(cond, b) => 1 + cond.size + b.size
    }

    // Simplified statement: by default do nothing
    def simplify: Statement = this
    def toPP: Statement = this

    // Is this an atomic statement?
    def isAtomic: Boolean = this match {
      case Skip => false
      case If(_,_,_,_) => false
      case Match(_,_,_) => false
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
      case If(_, _, tb, eb) => tb.atomicStatements ++ eb.atomicStatements
      case Match(_, _, arms) => arms.flatMap(_._2.atomicStatements).toList
      case Guarded(_, b) => b.atomicStatements
      case _ => List(this)
    }

    // Apply f to all atomic statements inside this statement
    def mapAtomic(f: Statement => Statement): Statement = this match {
      case SeqComp(s1, s2) => SeqComp(s1.mapAtomic(f), s2.mapAtomic(f))
      case If(r, cond, tb, eb) => If(r, cond, tb.mapAtomic(f), eb.mapAtomic(f))
      case Match(r, tgt, arms) => Match(r, tgt, arms.map(a => (a._1, a._2.mapAtomic(f))))
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
      case If(r, cond, tb, eb) => If(r,
        cond.resolveOverloading(gamma),
        tb.resolveOverloading(gamma),
        eb.resolveOverloading(gamma)
      )
      case Match(r, tgt, arms) => Match(r,
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
    def isRes: Boolean = this match {
      case Error => true
      case Construct(Var(""), _, _, _) => true
      case Call(Var("return "), _, _, _) => true
      case Call(_, List(Var("")), _, _) => true
      case Match(Var("") :: _, _, _) => true
      case If(Var("") :: _, _, _, _) => true
      case Store(_, 666, _) => true
      case _ => false
    }
  }

  // skip
  case object Skip extends Statement

  // ??
  case object Hole extends Statement

  // assert false
  case object Error extends Statement

  // substitute in future stmts
  case class Sub(sub: Subst) extends Statement

  // let to = malloc(n)
  case class Malloc(to: Var, tpe: SSLType, sz: Int = 1) extends Statement

  // free(v)
  case class Free(v: Var) extends Statement

  // let to = *from.offset
  case class Load(to: Var, tpe: SSLType, from: Var,
                  offset: Int = 0) extends Statement

  // let to = pred(args)
  case class Construct(to: Var, pred: Ident, variant: Option[String], args: Seq[Expr]) extends Statement {
    def cName: String = variant.getOrElse(pred)
    override def toPP: Statement = if (args.length == 0) Sub(Map(to -> Var(cName))) else this
  }

  // let results = match tgt { arms }
  case class Match(results: List[Var], tgt: Expr, arms: Seq[(Construct, Statement)]) extends Statement {
    override def simplify: Statement = {
      var armStmt: Option[Statement] = None
      for (arm <- arms if arm._2 != Error) {
        if (arm._1.args.size > 0 || armStmt.isDefined && armStmt.get != arm._2) return this
        armStmt = Some(arm._2)
      }
      if (armStmt.isEmpty) Error else armStmt.get
    }
  }

  // *to.offset = e
  case class Store(to: Expr, offset: Int, e: Expr) extends Statement

  // f(args)
  case class Call(fun: Var, result: List[Var], args: Seq[Expr], companion: Option[GoalLabel]) extends Statement

  // s1; s2
  case class SeqComp(s1: Statement, s2: Statement) extends Statement {
    override def simplify: Statement = (s1, s2) match {
      case (Skip, _) => s2 // Remove compositions with skip
      case (_, Skip) => s1
      case (Error, _) => Error
      case (_, Error) => Error
      case (SeqComp(s11, s12), s2) => SeqComp(s11, SeqComp(s12, s2).simplify) // Left-nested compositions are transformed to right-nested
      // Unused in Ruslik
      // case (_, Guarded(cond, b)) // Guards are propagated to the top but not beyond the definition of any var in their cond
      //     if cond.vars.intersect(s1.definedVars).isEmpty => Guarded(cond, SeqComp(s1, b).simplify)
      // case (Load(y, tpe, from, offset), _) => simplifyBinding(y, newY => Load(newY, tpe, from, offset))
      // case (Malloc(to, tpe, sz), _) => simplifyBinding(to, newTo => Malloc(newTo, tpe, sz))
      case _ => this
    }

    override def toPP: Statement = (s1.toPP, s2.toPP) match {
      // Subst:
      case (Sub(subst), s2) => s2.subst(subst)
      // Returns:
      case (Construct(to, pred, variant, args), Call(Var("return "), _, Seq(ret), _)) if to == ret =>
        Construct(Var(""), pred, variant, args)
      case (Call(fun, res, args, comp), Call(Var("return "), _, rets, _)) if res == rets =>
        Call(fun, List(Var("")), args, comp)
      case (If(res, cond, tb, fb), Call(Var("return "), _, rets, _)) if res.toSet == rets.toSet =>
        If(Var("") :: rets.map(_.asInstanceOf[Var]).toList, cond, tb, fb)
      case (Match(res, tgt, arms), Call(Var("return "), _, rets, _)) if res.toSet == rets.toSet =>
        Match(Var("") :: rets.map(_.asInstanceOf[Var]).toList, tgt, arms)
      case (Store(to, offset, e), Call(Var("return "), _, rets, _)) if rets.length == 0 =>
        Store(to, 666, e)
      // Any other Stmt should return the Unit with `;`
      case (s1, Call(Var("return "), _, rets, _)) if rets.length == 0 => s1
      case (s1, s2) => SeqComp(s1, s2)
    }

    // Eliminate or shorten newly bound variable newvar
    // depending on the rest of the program (s2)
    private def simplifyBinding(newvar: Var, mkBinding: Var => Statement): Statement =
      if (s2.vars.contains(newvar)) {
        val (v, s) = s2.simplifyVariable(newvar)
        SeqComp(mkBinding(v), s)
      } else s2  // Do not generate bindings for unused variables
  }

  // let results = if (cond) { tb } else { eb }
  case class If(results: List[Var], cond: Expr, tb: Statement, eb: Statement) extends Statement {
    override def simplify: Statement = {
      (tb, eb) match {
        case (Skip, Skip) =>
          assert(results.isEmpty)
          Skip
        case (Error, _) => eb.simplify
        case (_, Error) => tb.simplify
        case (Guarded(gcond, gb), eb) => Guarded(gcond, If(results, cond, gb, eb).simplify)
        case (tb, Guarded(gcond, gb)) => Guarded(gcond, If(results, cond, tb, gb).simplify)
        case _ => this
      }
    }
  }

  // assume cond { body } else { els }
  case class Guarded(cond: Expr, body: Statement) extends Statement {
    override def simplify: Statement = body.simplify match {
      case Guarded(c1, b1) => Guarded(cond && c1, b1)
      case body => Guarded(cond, body)
    }
  }

  // A procedure
  case class Procedure(f: FunSpec, body: Statement)(implicit predicates: Map[Ident, InductivePredicate]) {
    // val tmp = assert(body.vars.forall(_.name != ""))
    val (name: String, tp: SSLType, formals: Formals) = (f.name, f.rType, f.params)

    def pp: String = {
      val generics = if (f.lfts.size == 0) "" else s"<${f.lfts.mkString(", ")}>"
      val returns =
        if (f.rustReturns.length == 0) ""
        else if (f.rustReturns.length == 1) s"-> ${f.rustReturns.head._2.map(_.sig).mkString("")}${f.rustReturns.head._3} "
        else s"-> (${f.rustReturns.map(r => r._2.map(_.sig).mkString("") + r._3).mkString(", ")}) "
      s"""
          |fn $name$generics(${f.rustParams.map { case (f, r, t) => s"${f.pp}: ${r.map(_.sig).mkString("")}$t" }.mkString(", ")}) $returns{
          |  ${body.pp(f.result)}
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

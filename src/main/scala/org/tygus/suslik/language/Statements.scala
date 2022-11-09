package org.tygus.suslik.language

import org.tygus.suslik.logic.Specifications.GoalLabel
import org.tygus.suslik.logic.{Formals, RustFormals, FunSpec, Gamma}
import org.tygus.suslik.util.StringUtil._
import org.tygus.suslik.logic.InductivePredicate
import org.tygus.suslik.logic.Ref

/**
  * @author Ilya Sergey
  */
object Statements {

  import Expressions._

  sealed abstract class Statement extends HasExpressions[Statement] {

    // Pretty-printer
    def pp: String = {

      val builder = new StringBuilder

      def doRet(rets: Seq[Expr]): String = {
        if (rets.length > 0)
          if (rets.length == 1) rets(0).pp
          else rets.map(_.pp).mkString("(", ", ", ")")
        else "()"
      }

      def build(s: Statement, offset: Int = 2): Unit = {
        assert(s.simplify == s, "Simp: " + s.simplify + " vs " + s)
        s match {
          case Skip => builder.append("()")
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
            val structLike = c.structLike
            val bra = if (args.length == 0 || pred == "") "" else if (structLike) " { " else "("
            val ket = if (args.length == 0 || pred == "") "" else if (structLike) " }" else ")"
            builder.append(s"${if (c.isRes) "" else s"let ${to.get.pp} = "}${c.cName}$bra${c.argsPrint.map(_.pp).mkString(", ")}$ket${if (c.isRes) "" else ";"}")
          case m@Match(res, tgt, arms) =>
            val resStr = if (m.isRes) "" else s"let ${doRet(res.getRes)} = "
            builder.append(resStr).append(s"match ${tgt.pp} {\n")
            arms.map { case (constr, stmt) =>
              builder.append(mkSpaces(offset+2))
              build(constr, 0)
              builder.append(" => ")
              if (!stmt.isRes) builder.append("{\n" + mkSpaces(offset+4))
              build(stmt, offset + 4)
              if (!stmt.isRes) builder.append("\n" + mkSpaces(offset+2) + "}\n")
              else builder.append(",\n")
            }
            builder.append(mkSpaces(offset)).append(if (m.isRes) "}" else "};")
          case Return(ret) =>
            builder.append(doRet(ret.getRes))
          case c@Call(fun, result, args, _, rec, _) =>
            val resStr = if (c.isRes) "" else {
              val res = result.getRes
              if (res.forall(_.asInstanceOf[Var].name == "_")) "" else s"let ${doRet(result.getRes)} = "
            }
            val (receiver, cargs) = if (!rec) ("", args)
              else (BinaryExpr(OpField, UnaryExpr(OpDeRef, args.head).normalise, Var("")).normalise.pp, args.tail)
            val function_call = s"$resStr$receiver${fun.pp}(${cargs.map(_.pp).mkString(", ")})${if (c.isRes) "" else ";"}"
            builder.append(function_call)
          case SeqComp(s1,s2) =>
            build(s1, offset)
            builder.append("\n" + mkSpaces(offset))
            build(s2, offset)
          case i@If(rets, _, _, _) =>
            if (!i.isRes) builder.append(s"let ${doRet(rets.getRes)} = ")
            var ecase: Statement = i
            while (ecase match {
              case If(orets, cond, tb, eb) if rets.compareTo(orets) =>
                builder.append(s"if ${cond.pp} {")
                builder.append(if (!tb.isRes) "\n" + mkSpaces(offset+2) else " ")
                build(tb, offset + 2)
                builder.append(if (!tb.isRes) "\n" + mkSpaces(offset) else " ")
                builder.append("}")
                ecase = eb
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
      build(this)
      builder.toString()
    }

    // Expression-collector
    def collect[R <: Expr](p: Expr => Boolean): Set[R] = {

      def collector(acc: Set[R])(st: Statement): Set[R] = st match {
        case Skip => acc
        case Hole => acc
        case Error => acc
        case Sub(s) => acc
        case Store(to, off, e) =>
          acc ++ to.collect(p) ++ e.collect(p)
        case Load(_, _, from, off) =>
          acc ++ from.collect(p)
        case c@Construct(to, _, _, args) =>
          acc ++ to.map(_.collect(p)).getOrElse(Set.empty) ++ c.matchVars.flatMap(_.collect(p)).toSet
        case Match(r, tgt, arms) =>
          acc ++ r.getResSet.flatMap(_.collect(p)) ++ tgt.collect(p) ++
            arms.flatMap(a => a._1.matchVars.flatMap(_.collect(p)) ++ a._2.collect(p))
        case Malloc(_, _, _) =>
          acc
        case Free(x) =>
          acc ++ x.collect(p)
        case Call(fun, res, args, _, _, _) =>
          acc ++ fun.collect(p) ++ res.getResSet.flatMap(_.collect(p)).toSet ++ args.flatMap(_.collect(p)).toSet
        case Return(res) => acc ++ res.getExprSet.flatMap(_.collect(p)).toSet
        case SeqComp(s1,s2) =>
          val acc1 = collector(acc)(s1)
          collector(acc1)(s2)
        case If(r, cond, tb, eb) =>
          val acc1 = collector(acc  ++ r.getResSet.flatMap(_.collect(p)) ++ cond.collect(p))(tb)
          collector(acc1)(eb)
        case Guarded(cond, b) =>
          collector(acc ++ cond.collect(p))(b)
      }

      collector(Set.empty)(this)
    }

    override def subst(sigma: Subst): Statement = this match {
      case Construct(_, _, _, _) | SeqComp(_, _) => ???
      case Error | Hole | Skip => this
      case Store(to, off, e) => {
        Store(to.subst(sigma), off, e.subst(sigma))
      }
      case Load(to, tpe, from, offset) => {
        assert(!sigma.keySet.contains(to) || sigma(to).isInstanceOf[Var])
        assert(!sigma.keySet.contains(from) || sigma(from).isInstanceOf[Var])
        Load(to.subst(sigma).asInstanceOf[Var], tpe, from.subst(sigma).asInstanceOf[Var], offset)
      }
      case Sub(subst) => Sub(subst.mapValues(_.subst(sigma)))
      case Match(r, tgt, arms) =>
        Match(r, tgt.subst(sigma), arms.map(a => (a._1, a._2.subst(sigma))))
      case Malloc(to, tpe, sz) => {
        assert(!sigma.keySet.contains(to) || sigma(to).isInstanceOf[Var])
        Malloc(to.subst(sigma).asInstanceOf[Var], tpe, sz)
      }
      case Free(x) => {
        assert(!sigma.keySet.contains(x) || sigma(x).isInstanceOf[Var])
        Free(x.subst(sigma).asInstanceOf[Var])
      }
      case Return(ret) => Return(ret.subst(sigma))
      case c:Call => c.copy(args = c.args.map(_.subst(sigma)))
      case If(r, cond, tb, eb) => If(r, cond.subst(sigma), tb.subst(sigma), eb.subst(sigma))
      case Guarded(cond, b) => Guarded(cond.subst(sigma), b.subst(sigma))
    }
    def substRes(sigma: SubstVar): Statement = this match {
      case Construct(to, pred, variant, args) => {
        if (to.isDefined) assert(!sigma.keySet.contains(to.get) || sigma(to.get).isInstanceOf[Var])
        val newTo = to.map(_.varSubst(sigma).asInstanceOf[Var])
        if (newTo.isDefined && newTo.get.name == "_") Skip else
          Construct(newTo, pred, variant, args)
      }
      case Match(results, tgt, arms) => Match(results.varSubst(sigma), tgt, arms)
      case c:Call => c.copy(result = c.result.varSubst(sigma))
      // case SeqComp(s1, s2) => SeqComp(s1.substRes(sigma), s2.substRes(sigma))
      case If(results, cond, tb, eb) => If(results.varSubst(sigma), cond, tb, eb)
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
      case Construct(to, _, _, args) => 1 + to.map(_.size).getOrElse(0) + args.map(_._2.size + 1).sum
      case Match(to, tgt, arms) => 1 + to.getResSet.size + arms.map(a => a._1.size + a._2.size).sum
      case Malloc(to, _, _) => 1 + to.size
      case Free(x) => 1 + x.size
      case Call(_, res, args, _, _, _) => 1 + res.getResSet.size + args.map(_.size).sum
      case Return(res) => res.size
      case SeqComp(s1,s2) => s1.size + s2.size
      case If(_, cond, tb, eb) => 1 + cond.size + tb.size + eb.size
      case Guarded(cond, b) => 1 + cond.size + b.size
    }

    // Simplified statement: by default do nothing
    def simplify: Statement = this
    def doSubsts: Statement = this

    def simplifyVars(cmap: ClashMap, fname: String): (Statement, ClashMap) = this match {
      case Skip | Hole | Error | Malloc(_,_,_) | Free(_) | Load(_,_,_,_) => (this, cmap)
      case Sub(sub) => (this, cmap.subst(sub))
      case c:Construct => {
        val sub = doVarSimp(c.to.toSet, cmap)
        val newC = c.doResSimplify(sub)
        // Was turned into a skip?
        val unused = !(newC.isInstanceOf[SeqComp] || newC.isInstanceOf[Construct])
        if (unused) assert(c.pred == "")
        val argVars = if (unused) Set() else c.matchVars.flatMap(_.vars)
        (newC, cmap.dead(c.to.toSet).live(argVars.toSet))
      }
      case Match(results, tgt, arms) => {
        val resSet = results.getExprSet.flatMap(_.vars)
        val sub = doVarSimp(resSet, cmap)
        val (newArms, cmaps) = arms.map(a => {
          val (newStmt, cmap) = a._2.simplifyVars(ClashMap(Map.empty, Sub()), fname)
          val mVars = a._1.matchVars.map(_.asInstanceOf[Var]).toSet
          val sub = doVarSimp(mVars, cmap)
          ((a._1.subst(sub), SeqComp(Sub(sub).simplify, newStmt).simplify), cmap.dead(mVars))
        }).unzip
        val newCmap = cmaps.foldLeft(cmap.dead(resSet))(_ ++ _)
        (Match(results, tgt, newArms).doResSimplify(sub), newCmap.live(tgt.vars))
      }
      case If(results, cond, tb, eb) => {
        val resSet = results.getExprSet.flatMap(_.vars)
        val sub = doVarSimp(resSet, cmap)
        val (newEb, cmapEb) = eb.simplifyVars(ClashMap(Map.empty, Sub()), fname)
        val (newTb, cmapTb) = tb.simplifyVars(ClashMap(Map.empty, Sub()), fname)

        val newCmap = cmap.dead(resSet) ++ cmapEb ++ cmapTb
        (If(results, cond, newTb, newEb).doResSimplify(sub), newCmap.live(cond.vars))
      }
      case Store(to, offset, e) => (this, cmap.live(e.vars ++ to.vars))
      case Call(fun, results, args, _, _, _) => {
        val resSet = results.getExprSet.flatMap(_.vars)
        val sub = doVarSimp(resSet, cmap)
        val newCmap = if (fun.name == fname) cmap.dead(resSet).live(args.map(_.vars))
          else cmap.dead(resSet).live(args.flatMap(_.vars).toSet)
        if (results.r.isEmpty && !sub.isEmpty) println("What " + resSet)
        (this.doResSimplify(sub), newCmap)
      }
      case Return(ret) => (this, cmap.live(ret.getExprSet.flatMap(_.vars)))
      case SeqComp(s1, s2) => {
        val (newS2, cmapS2) = s2.simplifyVars(cmap, fname)
        val (newS1, cmapS1) = s1.simplifyVars(cmapS2, fname)
        (SeqComp(newS1, newS2).simplify, cmapS1)
      }
      case Guarded(cond, body) => ???
    }
    def doResSimplify(sub: SubstVar): Statement = if (sub.isEmpty) this
      // Unused vars getting subbed to "_" might as well not be subbed
      else SeqComp(this.substRes(sub), Sub(sub.filter(_._2.name != "_")).simplify).simplify

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
      case Call(_, _, _, Some(comp), _, _) => List(comp)
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
    def isRes: Boolean = this match {
      case Error => true
      case Skip => true
      case Construct(None, _, _, _) => true
      case Call(_, res, _, _, _, _) => res.r.isEmpty
      case Match(res, _, _) => res.r.isEmpty
      case If(res, _, _, _) => res.r.isEmpty
      case Store(_, 666, _) => true
      case Return(_) => true
      case _ => false
    }
    def hasRes: Boolean = this match {
      case SeqComp(_, s2) => s2.hasRes
      case _ => this.isRes
    }
    def withRes(rets: Results): Statement = SeqComp(this, Return(rets)).simplify.pushResIn
    def pushResIn: Statement = this
  }

  // skip
  case object Skip extends Statement

  // ??
  case object Hole extends Statement

  // assert false
  case object Error extends Statement

  // substitute in future stmts
  case class Sub(sub: Subst) extends Statement {
    override def simplify: Statement = if (sub.isEmpty) Skip else this
    override def doSubsts: Statement = Skip
  }
  object Sub {
    def apply(sub1: Subst, sub2: Subst): Sub = {
      var sub =  sub1 ++ sub2.mapValues(_.subst(sub1)).filter(m => m._1 != m._2)
      var oldSub: Subst = Map.empty
      var newSub = sub
      var i = 0
      while (newSub != oldSub && i < 5) {
        i += 1
        oldSub = newSub
        newSub = newSub.mapValues(_.subst(sub))
      }
      if (i >= 5) assert(false, "No fp with sub1 " + sub1 + " sub2 " + sub2)
      new Sub(newSub)
    }
    def apply(): Sub = new Sub(Map.empty)
  }

  // let to = malloc(n)
  case class Malloc(to: Var, tpe: SSLType, sz: Int = 1) extends Statement

  // free(v)
  case class Free(v: Var) extends Statement

  // return
  case class Return(res: Results) extends Statement

  // let to = *from.offset
  case class Load(to: Var, tpe: SSLType, from: Var,
                  offset: Int = 0) extends Statement

  // let to = pred(args)
  case class Construct(to: Option[Var], pred: Ident, variant: Option[String], args: Seq[(Var, Expr)]) extends Statement {
    def cName: String = variant.getOrElse(pred)
    override def simplify: Statement =
      if (args.isEmpty && to.isDefined) Sub(Map(to.get -> Var(cName))) else this
    def matchVars: Seq[Expr] =
      args.flatMap(a => {
        if (a._2.isInstanceOf[Var] && a._2.asInstanceOf[Var].name == "_") None
        else Some(a._2)
      })
    def structLike: Boolean = args.exists(!_._1.isTupleLike)
    def argsPrint: Seq[Expr] = {
      val ap = args.flatMap(a => {
        if (a._1.isTupleLike) Some(a._2)
        else if (a._2.isInstanceOf[Var] && a._2.asInstanceOf[Var].name == "_") None
        else Some(BinaryExpr(OpFieldBind, a._1, a._2).simplify)
      })
      if (ap.length != args.length) ap :+ Var("..") else ap
    }
    override def subst(sigma: Subst): Construct = {
      if (to.isDefined) assert(!sigma.keySet.contains(to.get) || sigma(to.get).isInstanceOf[Var])
      Construct(to.map(_.subst(sigma).asInstanceOf[Var]), pred, variant, args.map(a => (a._1, a._2.subst(sigma))))
    }
  }

  // let results = match tgt { arms }
  case class Match(results: Results, tgt: Expr, arms: Seq[(Construct, Statement)]) extends Statement {
    override def simplify: Statement = {
      if (arms.length == 0) return this
      var armStmt: Option[Statement] = None
      for (arm <- arms if arm._2 != Error) {
        // TODO: two Returns might still be != even if they were the same due to differing subs
        if (arm._1.args.filter(a => !a._2.isInstanceOf[Var] || a._2.asInstanceOf[Var].name != "_").length > 0 ||
            (armStmt.isDefined && armStmt.get != arm._2)) return this
        armStmt = Some(arm._2)
      }
      if (armStmt.isEmpty) Error else armStmt.get
    }
    def addResToArms(res: Results): Match = {
      if (res.r.isEmpty) this
      else this.copy(arms = this.arms.map(a => (a._1, a._2.withRes(res))))
    }
    override def doSubsts: Statement = {
      this.copy(arms = this.arms.map(a => (a._1, a._2.doSubsts))).simplify
    }
    
    override def pushResIn: Statement = this.addResToArms(results)
  }

  // *to.offset = e
  case class Store(to: Expr, offset: Int, e: Expr) extends Statement

  // f(args)
  case class Call(fun: Var, result: Results, args: Seq[Expr], companion: Option[GoalLabel], hasReceiver: Boolean, callGoal: Statement) extends Statement

  // s1; s2
  case class SeqComp(s1: Statement, s2: Statement) extends Statement {
    override def simplify: Statement = (s1, s2) match {
      // Move compositions into callGoal
      case (s1, c:Call) if c.callGoal != Hole => c.copy(callGoal = SeqComp(s1, c.callGoal).simplify)
      case (s1, SeqComp(c:Call, s2)) if c.callGoal != Hole =>
        SeqComp(c.copy(callGoal = SeqComp(s1, c.callGoal).simplify), s2)
      case (SeqComp(c:Call, s1), s2) if c.callGoal != Hole =>
        SeqComp(c.copy(callGoal = SeqComp(c.callGoal, s2).simplify), s1)
      // Preserve skip after unfinished call
      case (c:Call, Skip) if c.callGoal != Hole => this
      // Normal:
      case (Skip, _) => s2 // Remove compositions with skip
      case (_, Skip) => s1
        // Don't simplify errors so that we can see how they were reached
      case (Error, s2) => SeqComp(s2, Error).simplify
      case (Return(_), Error) => Error
      // case (Error, _) => Error
      // case (_, Error) => Error
      case (Sub(subst1), Sub(subst2)) => Sub(subst1, subst2)
      case (Sub(subst1), SeqComp(Sub(subst2), s2)) =>
        SeqComp(Sub(subst1, subst2), s2)
      // case (s1, s2:Sub) if !s1.isInstanceOf[Sub] => SeqComp(s2, s1)
      // Left-nested compositions are transformed to right-nested
      case (SeqComp(s11, s12), s2) => SeqComp(s11, SeqComp(s12, s2).simplify).simplify
      // Unused in Ruslik
      // case (_, Guarded(cond, b)) // Guards are propagated to the top but not beyond the definition of any var in their cond
      //     if cond.vars.intersect(s1.definedVars).isEmpty => Guarded(cond, SeqComp(s1, b).simplify)
      // case (Load(y, tpe, from, offset), _) => simplifyBinding(y, newY => Load(newY, tpe, from, offset))
      // case (Malloc(to, tpe, sz), _) => simplifyBinding(to, newTo => Malloc(newTo, tpe, sz))
      // Returns:
      case (Construct(to, pred, variant, args), Return(ret)) if to.toSet == ret.getExprSet =>
        Construct(None, pred, variant, args)
      case (c:Call, Return(ret)) if c.result.compareTo(ret) =>
        c.copy(result = Results())
      case (If(res, cond, tb, fb), Return(ret)) if res.compareTo(ret) =>
        If(Results(), cond, tb, fb).addResToArms(ret)
      case (Match(res, tgt, arms), Return(ret)) if res.compareTo(ret) =>
        Match(Results(), tgt, arms).addResToArms(ret)
      case (Store(to, offset, e), Return(ret)) if ret.isEmpty =>
        Store(to, 666, e)
      // Any other Stmt should return the Unit with `;`
      case (s1, Return(ret)) if ret.isEmpty => s1
      case _ => this
    }
    override def doSubsts: Statement = s1 match {
      case Sub(subst) => s2.subst(subst).doSubsts
      case _ => SeqComp(s1.doSubsts, s2.doSubsts).simplify
    }
    override def subst(sigma: Subst): SeqComp = SeqComp(s1.subst(sigma), s2.subst(sigma))

    // Eliminate or shorten newly bound variable newvar
    // depending on the rest of the program (s2)
    private def simplifyBinding(newvar: Var, mkBinding: Var => Statement): Statement =
      if (s2.vars.contains(newvar)) {
        val (v, s) = s2.simplifyVariable(newvar)
        SeqComp(mkBinding(v), s)
      } else s2  // Do not generate bindings for unused variables

    override def pushResIn: Statement = SeqComp(s1.pushResIn, s2.pushResIn)
  }

  // let results = if (cond) { tb } else { eb }
  case class If(results: Results, cond: Expr, tb: Statement, eb: Statement) extends Statement {
    override def simplify: Statement = {
      (tb, eb) match {
        case (Skip, Skip) =>
          assert(results.isEmpty)
          Skip
        case (Error, _) => eb
        case (_, Error) => tb
        case (Guarded(gcond, gb), eb) => Guarded(gcond, If(results, cond, gb, eb).simplify)
        case (tb, Guarded(gcond, gb)) => Guarded(gcond, If(results, cond, tb, gb).simplify)
        case _ => this
      }
    }
    def addResToArms(res: Results): If = {
      if (res.r.isEmpty) this
      else If(results, cond, tb.withRes(res), eb.withRes(res))
    }
    override def doSubsts: If = this.copy(tb = tb.doSubsts, eb = eb.doSubsts)
    override def pushResIn: Statement = this.addResToArms(results)
  }

  // assume cond { body } else { els }
  case class Guarded(cond: Expr, body: Statement) extends Statement {
    override def simplify: Statement = body.simplify match {
      case Guarded(c1, b1) => Guarded(cond && c1, b1)
      case body => Guarded(cond, body)
    }
  }

  def doVarSimp(vars: Set[Var], cmap: ClashMap): SubstVar = if (vars.isEmpty) Map.empty
    else {
      val live = cmap.cmap
      vars.map(v => v -> {
        if (!live.contains(v)) Var("_")
        else {
          val blocking = live(v)._2 - v
          val parts = v.name.split('_')
          var i = if (parts(0) == "") 2 else 1
          while (i < parts.length && blocking.exists(b => 
            b.name.startsWith(parts.take(i).mkString("_")) && b.name.split('_').length <= parts.length
          )) {
            i += 1
          }
          Var(parts.take(i).mkString("_"))
        }
      }).filter(sub => sub._1 != sub._2).toMap
    }


  // A procedure
  case class Procedure(f: FunSpec, body: Statement, unsimpBody: Statement)(implicit predicates: Map[Ident, InductivePredicate]) {
    val (name: String, formals: Formals, returns: RustFormals) = (f.clean, f.params, f.rustReturns)

    def ppWithHelpers(helpers: List[Procedure]): String = {
      val helpersStr = helpers.map("\n#[helper]\n" + _.pp).mkString("").replace("\n", "\n  ")
      s"""|$ppSig {$helpersStr
          |  ${body.pp}
          |}""".stripMargin
    }
    def pp: String = {
      s"""|$ppSig {
          |  ${body.pp}
          |}""".stripMargin
    }
    def ppSig: String = {
      val lfts = f.lfts.filter(lft => !lft.startsWith("'_") && lft != "'static")
      val generics = if (lfts.size == 0) "" else s"<${lfts.mkString(", ")}>"
      val returnStr =
        if (returns.length == 0) ""
        else if (returns.length == 1) s" -> ${returns.head._2.map(_.sig).mkString("")}${returns.head._3}"
        else s" -> (${returns.map(r => r._2.map(_.sig).mkString("") + r._3).mkString(", ")})"
      s"fn $name$generics(${f.rustParams.map { case (f, r, t) => formalPp(f,r,t) }.mkString(", ")})$returnStr"
    }
    def formalPp(f: Var, r: List[Ref], t: Ident): String =
      if (f.name == "self") s"${r.map(_.sig).mkString("")}${f.pp}"
      else s"${f.pp}: ${r.map(_.sig).mkString("")}$t"

    // def ppOld: String =
    //   s"""
    //      |${tp.pp} $name (${formals.map { case (i, t) => s"${t.pp} ${i.pp}" }.mkString(", ")}) {
    //      |${body.pp(f.result)}
    //      |}
    // """.stripMargin

    def subst(sub: Sub) = this.copy(body = body.subst(sub.sub))
  }
  object Procedure {
    def apply(f: FunSpec, body: Statement)(implicit predicates: Map[Ident, InductivePredicate]): (Procedure, Map[Int,Boolean]) = {
      val argsFixed = f.returns.r.get._1.res.res.isInstanceOf[OrderedRes]
      val procBody = body.withRes(f.returns).doSubsts
      val _newBody = procBody.simplifyVars(ClashMap(Map.empty, Sub()), f.name)._1.doSubsts
      // Run this twice to get rid of unnecessary matches first and then unused vars second
      val (newBody, cmap) = _newBody.simplifyVars(ClashMap(Map.empty, Sub()), f.name)

      val argNames = f.params.map(_._1)
      // To skip simplification use the following cmap
      // val newBody = procBody
      // val cmap = ClashMap(argNames.map(a => a -> (Set.empty[Int], argNames.toSet)).toMap, Sub())
      val sub: SubstVar = if (argsFixed) Map.empty else doVarSimp(argNames.toSet, cmap)
      var oldUsedArgs = Map.empty[Int, Boolean]
      var usedArgs = f.params.indices.map(_ -> argsFixed).toMap
      while (oldUsedArgs != usedArgs) {
        oldUsedArgs = usedArgs
        usedArgs = usedArgs.map(a => a._1 -> {
          val param = f.params(a._1)._1
          a._2 || (cmap.cmap.contains(param) &&
            (cmap.cmap(param)._1.isEmpty || cmap.cmap(param)._1.exists(!usedArgs(_))))
        })
      }
      val newF = f.copy(rustParams =
        f.rustParams.zipWithIndex.filter(p => usedArgs(p._2)).map(
          p => (p._1._1.varSubst(sub), p._1._2, predicates(p._1._3).clean)
        )
      )
      (new Procedure(newF, SeqComp(Sub(sub), newBody).simplify.doSubsts, procBody), usedArgs)
    }
    def apply(f: FunSpec, body: Statement, outerCall: Call)(implicit predicates: Map[Ident, InductivePredicate]): (Procedure, Call) = {
      val (proc, usedArgs) = Procedure(f, body)
      val newArgs = outerCall.args.indices.filter(usedArgs).map(i => outerCall.args(i))
      (proc, outerCall.copy(args = newArgs, callGoal = Hole))
    }
  }

  // Solution for a synthesis goal:
  // a statement and a possibly empty list of recursive helpers
  type Solution = (Statement, List[Procedure])

  case class Results(r: Option[(FnResList, Sub, SubstVar)] = None) {
    override def equals(that: Any): Boolean = that match {
        case other: Results => {
          if (this.r.isDefined != other.r.isDefined) return false
          if (this.r.isEmpty && other.r.isEmpty) return true
          val (sub1, sub2) = (this.sub ++ this.subVar, other.sub ++ other.subVar)
          (this.res, other.res) match {
            case (OrderedRes(res1), OrderedRes(res2)) => res1.map(_.subst(sub1)) == res2.map(_.subst(sub2))
            case (UnorderedRes(res1), UnorderedRes(res2)) => res1.map(_.subst(sub1)) == res2.map(_.subst(sub2))
            case _ => false
          }
        }
        case _ => false
    }

    def res: ResList = r.get._1.res.res
    def sub: Subst = r.get._2.sub
    def subVar: SubstVar = r.get._3
    // var res: ResList = OrderedRes(Nil)
    // var subst: Subst = Map.empty
    def isEmpty: Boolean = res.getResSet.isEmpty
    def compareTo(other: Results): Boolean = {
      if (this.r.isDefined != other.r.isDefined) return false
      if (this.r.isEmpty && other.r.isEmpty) return true
      val (sub1, sub2) = (this.sub ++ this.subVar, other.sub ++ other.subVar)
      (this.res, other.res) match {
        case (OrderedRes(res1), OrderedRes(res2)) => res1.map(_.subst(sub1)) == res2.map(_.subst(sub2))
        case (res1, res2) =>
          if (res1.getResSet.map(_.subst(sub1)) == res2.getResSet.map(_.subst(sub2))) {
            val (unord, unordSub, ordList) = if (res2.isInstanceOf[OrderedRes])
              (this.r.get._1, sub1, res2.asInstanceOf[OrderedRes].res.map(_.subst(sub2)))
            else {
              val newRes = res.getRes
              this.r.get._1.res.res = newRes
              (other.r.get._1, sub2, newRes.res.map(_.subst(sub1)))
            }
            val unordMap = unord.res.res.getResSet.map(r => r.subst(unordSub) -> r).toMap
            unord.res.res = OrderedRes(ordList.map(unordMap))
            true
          } else false
      }
    }
    def size: Int = res.getResSet.size
    def getResSet: Set[Var] = {
      if (this.r.isEmpty) Set.empty else {
        assert(this.sub.isEmpty)
        res.getResSet.map(_.varSubst(subVar))
      }
    }
    def getExprSet: Set[Expr] = {
      if (this.r.isEmpty) Set.empty else {
        res.getResSet.map(_.subst(sub ++ subVar))
      }
    }
    def getRes: Seq[Expr] = {
      val newRes = res.getRes
      this.r.get._1.res.res = newRes
      newRes.res.map(_.varSubst(subVar).subst(sub))
    }
    def getResNoSub: Seq[Var] = {
      val newRes = res.getRes
      this.r.get._1.res.res = newRes
      newRes.res
    }
    def varSubst(subst: SubstVar): Results = {
      assert(sub.isEmpty && subVar.isEmpty, "Adding " + subst + "\nBut already have" + sub + " and " + subVar)
      Results(Some(this.r.get.copy(_3 = subst)))
    }
    def subst(sigma: Subst): Results = {
      assert(r.isEmpty || subVar.isEmpty)
      Results(Some(this.r.get.copy(_2 = Sub(sub.mapValues(_.subst(sigma)) ++ sigma))))
    }
  }
  object Results {
    def apply(res: FnResList): Results = new Results(Some(res, Sub(), Map.empty))
  }

  // All results that should be initially equal will point to the same this object
  class FnResList {
    var res: EqualityResList = new EqualityResList()
  }
  // All `FnResList`s that should be equal will point to the same this object
  class EqualityResList {
    var res: ResList = OrderedRes(Nil)
  }
  object FnResList {
    def apply(): FnResList = new FnResList()
    def apply(res: Seq[Var]): FnResList = {
      val nr = new FnResList()
      nr.res.res = OrderedRes(res)
      nr
    }
    def apply(res: Set[Var]): FnResList = {
      val nr = new FnResList()
      nr.res.res = UnorderedRes(res)
      nr
    }
  }
  sealed abstract class ResList {
    def getResSet: Set[Var]
    def getRes: OrderedRes
    def varSubst(subst: SubstVar): ResList
  }
  case class OrderedRes(res: Seq[Var]) extends ResList {
    override def getResSet: Set[Var] = this.res.toSet
    override def getRes: OrderedRes = this
    override def varSubst(subst: SubstVar): OrderedRes = OrderedRes(res.map(_.varSubst(subst)))
  }
  case class UnorderedRes(res: Set[Var]) extends ResList {
    override def getResSet: Set[Var] = this.res
    override def getRes: OrderedRes = OrderedRes(res.toSeq)
    override def varSubst(subst: SubstVar): UnorderedRes = UnorderedRes(res.map(_.varSubst(subst)))
  }

  type CMap = Map[Var, (Set[Int], Set[Var])]
  case class ClashMap(live: CMap, subst: Sub) {
    def live(vs: Set[Var]): ClashMap =
      ClashMap(merge(live.mapValues(v => (v._1, v._2 ++ vs)), vs.map(_ -> (Set.empty[Int], live.keySet ++ vs)).toMap), subst)
    def live(vs: Seq[Set[Var]]): ClashMap =
      ClashMap(merge(live.mapValues(v => (v._1, v._2 ++ vs.flatten)),
        merge(vs.zipWithIndex.map(v => v._1.map(_ -> (Set(v._2), live.keySet ++ vs.flatten)).toMap))), subst)
    def dead(vs: Set[Var]): ClashMap = ClashMap(live -- vs, subst)
    def subst(sub: Subst): ClashMap = {
      val newSub = Sub(subst.sub ++ sub)
      ClashMap(ClashMap(live, newSub).cmap, newSub)
    }
    def cmap: CMap = merge(live.map{case (v, bs) =>
      subst.sub.getOrElse(v,v).vars.map(_ -> (bs._1, bs._2.flatMap(b => subst.sub.getOrElse(b,b).vars))).toMap
    })
    def ++(other: ClashMap) = ClashMap(merge(this.cmap, other.cmap), Sub())

    def merge(m1: CMap, m2: CMap): CMap = merge(Seq(m1, m2))
    def merge(ms: Iterable[CMap]): CMap =
      ms.foldLeft(Map.empty[Var, (Set[Int], Set[Var])])((l, r) => r.foldLeft(l)((l, r) =>
        l + (if (l.contains(r._1)) r._1 -> (
          if (l(r._1)._1.isEmpty || r._2._1.isEmpty) Set.empty
          else l(r._1)._1 ++ r._2._1
        , l(r._1)._2 ++ r._2._2) else r)
      ))
  }
}

package org.tygus.suslik.language

import org.tygus.suslik.logic.{Gamma, PureLogicUtils}
import org.tygus.suslik.synthesis.SynthesisException

/**
  * @author Ilya Sergey
  */

object Expressions {

  sealed abstract class UnOp extends PrettyPrinting {
    def level: Int = 5
    def inputType: SSLType
    def outputType: SSLType
    def postfix: Boolean = false
  }
  object OpNot extends UnOp {
    override def pp: String = "not "
    override def inputType: SSLType = BoolType
    override def outputType: SSLType = BoolType
  }

  object OpUnaryMinus extends UnOp {
    override def pp: String = "-"
    override def inputType: SSLType = IntType
    override def outputType: SSLType = IntType
  }

  object OpLower extends UnOp {
    override def pp: String = "lower "
    override def inputType: SSLType = IntervalType
    override def outputType: SSLType = IntType
  }

  object OpUpper extends UnOp {
    override def pp: String = "upper "
    override def inputType: SSLType = IntervalType
    override def outputType: SSLType = IntType
  }

  case class OpTakeRef(mut: Boolean) extends UnOp {
    override def pp: String = if (mut) "&mut " else "&"
    override def inputType: SSLType = LocType
    override def outputType: SSLType = LocType
  }
  object OpDeRef extends UnOp with AssociativeOp {
    override def level: Int = 6
    override def pp: String = "*"
    override def inputType: SSLType = LocType
    override def outputType: SSLType = LocType
  }
  case class OpCast(tp: String) extends UnOp {
    override def pp: String = " as " + tp
    override def inputType: SSLType = LocType
    override def outputType: SSLType = LocType
    override def postfix: Boolean = true
  }

  sealed abstract class BinOp extends OverloadedBinOp {
    def lType:SSLType
    def rType: SSLType

    override def opFromTypes: Map[(SSLType, SSLType), BinOp] = Map((lType, rType) -> this)

    override def default: BinOp = this

    def resType: SSLType
    def ppSpace: String = " "
  }

  sealed abstract class OverloadedBinOp extends PrettyPrinting {
    def opFromTypes: Map[(SSLType, SSLType), BinOp]
    def default: BinOp
    def level:Int
  }

  sealed abstract class RelOp extends BinOp {
    def resType: SSLType = BoolType
  }
  sealed abstract class LogicOp extends BinOp {
    def lType: SSLType = BoolType
    def rType: SSLType = BoolType
    def resType: SSLType = BoolType
  }
  trait SymmetricOp
  trait AssociativeOp

  object OpOverloadedEq extends OverloadedBinOp {
    override def level: Int = 3
    override def pp: String = "=="
    override def opFromTypes: Map[(SSLType, SSLType), BinOp] = Map(
      (IntType, IntType) -> OpEq,
      (LocType, LocType) -> OpEq,
      (IntSetType, IntSetType) -> OpSetEq,
      (IntervalType, IntervalType) -> OpIntervalEq,
      (BoolType, BoolType) -> OpBoolEq,
      (LifetimeType, LifetimeType) -> OpLftEq,
    )

    override def default: BinOp = OpEq
  }

  object OpNotEqual extends OverloadedBinOp {
    // some not implemented, because it is syntactic sugar operator, and shouldn't be met after Parser
    override def opFromTypes: Map[(SSLType, SSLType), BinOp] = ???
    override def default: BinOp = ???
    override def level: Int = 3
    override def pp: String = "!="
  }

  object OpGt extends OverloadedBinOp {
    // some not implemented, because it is syntactic sugar operator, and shouldn't be met after Parser
    override def opFromTypes: Map[(SSLType, SSLType), BinOp] = ???
    override def default: BinOp = ???
    override def level: Int = 3
    override def pp: String = ">"
  }

  object OpGeq extends OverloadedBinOp {
    // some not implemented, because it is syntactic sugar operator, and shouldn't be met after Parser
    override def opFromTypes: Map[(SSLType, SSLType), BinOp] = ???
    override def default: BinOp = ???
    override def level: Int = 3
    override def pp: String = ">="
  }

  object OpImplication extends BinOp {
    override def level: Int = 3
    override def pp: String = "==>"

    override def lType: SSLType = BoolType
    override def rType: SSLType = BoolType
    override def resType: SSLType = BoolType
  }

  object OpOverloadedIn extends OverloadedBinOp {
    override def level: Int = 3
    override def pp: String = "in"
    override def opFromTypes: Map[(SSLType, SSLType), BinOp] = Map(
      (IntType, IntSetType) -> OpIn,
      (IntType, IntervalType) -> OpIntervalIn,
    )

    override def default: BinOp = OpIn
  }


  object OpOverloadedPlus extends OverloadedBinOp {
    override def level: Int = 4
    override def pp: String = "+"
    override def opFromTypes: Map[(SSLType, SSLType), BinOp] = Map(
      (IntType, IntType) -> OpPlus,
      (IntSetType, IntSetType) -> OpUnion,
      (IntervalType, IntervalType) -> OpIntervalUnion,
    )

    override def default: BinOp = OpPlus
  }

  object OpOverloadedMinus extends OverloadedBinOp {
    override def level: Int = 4
    override def pp: String = "-"
    override def opFromTypes: Map[(SSLType, SSLType), BinOp] = Map(
      (IntType, IntType) -> OpMinus,
      (IntSetType, IntSetType) -> OpDiff,
    )

    override def default: BinOp = OpMinus
  }

  object OpOverloadedLeq extends OverloadedBinOp {
    override def level: Int = 3
    override def pp: String = "<=ovr"
    override def opFromTypes: Map[(SSLType, SSLType), BinOp] = Map(
      (IntType, IntType) -> OpLeq,
      (LifetimeType, LifetimeType) -> OpOutlived,
      (IntSetType, IntSetType) -> OpSubset,
      (IntervalType, IntervalType) -> OpSubinterval,
    )

    override def default: BinOp = OpLeq
  }

  object OpOverloadedStar extends OverloadedBinOp {
    override def level: Int = 4
    override def pp: String = "*"
    override def opFromTypes: Map[(SSLType, SSLType), BinOp] = Map(
      (IntType, IntType) -> OpMultiply,
      (IntSetType, IntSetType) -> OpIntersect,
    )

    override def default: BinOp = OpLeq
  }

  object OpPlus extends BinOp with SymmetricOp with AssociativeOp {
    def level: Int = 4
    override def pp: String = "+"
    def lType: SSLType = IntType
    def rType: SSLType = IntType
    def resType: SSLType = IntType
  }
  object OpMinus extends BinOp {
    def level: Int = 4
    override def pp: String = "-"
    def lType: SSLType = IntType
    def rType: SSLType = IntType
    def resType: SSLType = IntType
  }
  object OpMultiply extends BinOp {
    def level: Int = 4
    override def pp: String = "*"
    def lType: SSLType = IntType
    def rType: SSLType = IntType
    def resType: SSLType = IntType
  }
  object OpEq extends RelOp with SymmetricOp {
    def level: Int = 3
    override def pp: String = "=="
    def lType: SSLType = LocType
    def rType: SSLType = LocType
  }

  object OpBoolEq extends RelOp with SymmetricOp {
    def level: Int = 3
    override def pp: String = "=="
    def lType: SSLType = BoolType
    def rType: SSLType = BoolType
  }

  object OpLftEq extends RelOp with SymmetricOp {
    def level: Int = 3
    override def pp: String = "=="
    def lType: SSLType = LifetimeType
    def rType: SSLType = LifetimeType
  }

  object OpLeq extends RelOp {
    def level: Int = 3
    override def pp: String = "<="
    def lType: SSLType = IntType
    def rType: SSLType = IntType
  }
  object OpLt extends RelOp {
    def level: Int = 3
    override def pp: String = "<"
    def lType: SSLType = IntType
    def rType: SSLType = IntType
  }
  object OpAnd extends LogicOp with SymmetricOp with AssociativeOp {
    def level: Int = 2
    override def pp: String = "&&"
  }
  object OpOr extends LogicOp with SymmetricOp with AssociativeOp {
    def level: Int = 1
    override def pp: String = "||"
  }
  object OpUnion extends BinOp with SymmetricOp with AssociativeOp {
    def level: Int = 4
    override def pp: String = "++"
    def lType: SSLType = IntSetType
    def rType: SSLType = IntSetType
    def resType: SSLType = IntSetType
  }
  object OpDiff extends BinOp {
    def level: Int = 4
    override def pp: String = "--"
    def lType: SSLType = IntSetType
    def rType: SSLType = IntSetType
    def resType: SSLType = IntSetType
  }
  object OpIn extends RelOp {
    def level: Int = 3
    override def pp: String = "in"
    def lType: SSLType = IntType
    def rType: SSLType = IntSetType
  }
  object OpSetEq extends RelOp with SymmetricOp {
    def level: Int = 3
    override def pp: String = "=i"
    def lType: SSLType = IntSetType
    def rType: SSLType = IntSetType
  }
  object OpSubset extends RelOp {
    def level: Int = 3
    override def pp: String = "<=i"
    def lType: SSLType = IntSetType
    def rType: SSLType = IntSetType
  }
  object OpIntersect extends BinOp with SymmetricOp with AssociativeOp {
    def level: Int = 4
    override def pp: String = "*"
    def lType: SSLType = IntSetType
    def rType: SSLType = IntSetType
    override def resType: SSLType = IntSetType
  }

  object OpRange extends BinOp {
    def level: Int = 5
    override def pp: String = ".."
    def lType: SSLType = IntType
    def rType: SSLType = IntType
    override def resType: SSLType = IntervalType
  }
  object OpIntervalUnion extends BinOp with SymmetricOp with AssociativeOp {
    def level: Int = 4
    override def pp: String = "++"
    def lType: SSLType = IntervalType
    def rType: SSLType = IntervalType
    def resType: SSLType = IntervalType
  }
  object OpIntervalIn extends RelOp {
    def level: Int = 3
    override def pp: String = "in"
    def lType: SSLType = IntType
    def rType: SSLType = IntervalType
  }
  object OpIntervalEq extends RelOp with SymmetricOp {
    def level: Int = 3
    override def pp: String = "=="
    def lType: SSLType = IntervalType
    def rType: SSLType = IntervalType
  }
  object OpSubinterval extends RelOp {
    def level: Int = 3
    override def pp: String = "<="
    def lType: SSLType = IntervalType
    def rType: SSLType = IntervalType
  }
  object OpOutlived extends RelOp {
    def level: Int = 3
    override def pp: String = "<="
    def lType: SSLType = LifetimeType
    def rType: SSLType = LifetimeType
  }
  // Associative since rhs is always Var
  object OpField extends BinOp with AssociativeOp {
    override def level: Int = 7
    override def pp: String = "."
    def lType: SSLType = LocType
    def rType: SSLType = LocType
    override def resType: SSLType = LocType
    override def ppSpace: String = ""
  }
  object OpFieldBind extends BinOp {
    override def level: Int = 0
    override def pp: String = ": "
    def lType: SSLType = LocType
    def rType: SSLType = LocType
    override def resType: SSLType = LocType
    override def ppSpace: String = ""
  }


  sealed abstract class Expr extends PrettyPrinting with HasExpressions[Expr] with Ordered[Expr] with PureLogicUtils {

    def compare(that: Expr): Int = this.pp.compare(that.pp)

    // Type-coercing visitor (yikes!)
    def collect[R <: Expr](p: Expr => Boolean): Set[R] = {

      def collector(acc: Set[R])(exp: Expr): Set[R] = exp match {
        case v@Var(_) if p(v) => acc + v.asInstanceOf[R]
        case ae@AlwaysExistsVar(v) => {
          val acc1 = if (p(ae)) acc + ae.asInstanceOf[R] else acc
          collector(acc1)(v)
        }
        case n@NoExists(e) =>
          val acc1 = if (p(n)) acc + n.asInstanceOf[R] else acc
          collector(acc1)(e)
        case e@OnExpiry(_, _, _, _, _) if p(e) => acc + e.asInstanceOf[R]
        case n@Named(v, _) => {
          val acc1 = if (p(n)) acc + n.asInstanceOf[R] else acc
          collector(acc1)(v)
        }
        case t@TupleExpr(exprs) =>
          val acc1 = if (p(t)) acc + t.asInstanceOf[R] else acc
          exprs.foldLeft(acc1)((a,e) => collector(a)(e._1))
        case StaticLifetime if p(StaticLifetime) => acc + StaticLifetime.asInstanceOf[R]
        case NilLifetime if p(NilLifetime) => acc + NilLifetime.asInstanceOf[R]
        case c@IntConst(_) if p(c) => acc + c.asInstanceOf[R]
        case c@LocConst(_) if p(c) => acc + c.asInstanceOf[R]
        case c@BoolConst(_) if p(c) => acc + c.asInstanceOf[R]
        case b@BinaryExpr(op, l, r) =>
          val acc1 = if (p(b)) acc + b.asInstanceOf[R] else acc
          val acc2 = collector(acc1)(l)
          if (op == OpField) acc2 else collector(acc2)(r)
        case b@OverloadedBinaryExpr(_, l, r) =>
          val acc1 = if (p(b)) acc + b.asInstanceOf[R] else acc
          val acc2 = collector(acc1)(l)
          collector(acc2)(r)
        case u@UnaryExpr(_, arg) =>
          val acc1 = if (p(u)) acc + u.asInstanceOf[R] else acc
          collector(acc1)(arg)
        case s@SetLiteral(elems) =>
          val acc1 = if (p(s)) acc + s.asInstanceOf[R] else acc
          elems.foldLeft(acc1)((a,e) => collector(a)(e))
        case i@IfThenElse(cond, l, r) =>
          val acc1 = if (p(i)) acc + i.asInstanceOf[R] else acc
          val acc2 = collector(acc1)(cond)
          val acc3 = collector(acc2)(l)
          collector(acc3)(r)
        case c@Unknown(_,params,_) =>
          val acc1 = if (p(c)) acc + c.asInstanceOf[R] else acc
          params.foldLeft(acc1)((a,e) => collector(a)(e))
        case _ => acc
      }

      collector(Set.empty)(this)
    }

    def level: Int = 9
    def associative: Boolean = false

    def printInContext(parent: Expr): String = {
      val s = pp
      if (parent.level < this.level) s
      else this match {
        case expr: BinaryExpr if associative && parent.isInstanceOf[BinaryExpr] && expr.op == parent.asInstanceOf[BinaryExpr].op => s
        case expr: UnaryExpr if associative && parent.isInstanceOf[UnaryExpr] && expr.op == parent.asInstanceOf[UnaryExpr].op => s
        case _ => s"($s)"
      }
    }

    // Convenience operators for building expressions
    def |=| (other: Expr): Expr = BinaryExpr(OpEq, this, other)
    def |+| (other: Expr): Expr = BinaryExpr(OpPlus, this, other)
    def |===| (other: Expr): Expr = OverloadedBinaryExpr(OpOverloadedEq, this, other)
    def |/=| (other: Expr): Expr = (this |=| other).not
    def |/===| (other: Expr): Expr = (this |===| other).not
    def eq(other: Expr, t: SSLType): Expr = t match {
      case IntSetType => BinaryExpr(OpSetEq, this, other)
      case BoolType => this <==> other
      case _ => this |=| other
    }
    def neq(other: Expr, t: SSLType): Expr = this.eq(other, t).not
    def |<=| (other: Expr): Expr = BinaryExpr(OpLeq, this, other)

    def not: Expr = UnaryExpr(OpNot, this)
    def && (other: Expr): Expr = BinaryExpr(OpAnd, this, other)
    def || (other: Expr): Expr = BinaryExpr(OpOr, this, other)
    def ==> (other: Expr): Expr = this.not || other
    def <==> (other: Expr): Expr = (this ==> other) && (other ==> this)

    def getType(gamma: Gamma): Option[SSLType]

    def substUnknown(sigma: UnknownSubst): Expr = this

    def resolve(gamma: Gamma, target: Option[SSLType]): Option[Gamma] = this match {
      case v@Var(_) if v.name.endsWith("-L") => if (LifetimeType.conformsTo(target)) Some(gamma + (v -> LifetimeType)) else None
      case ae@AlwaysExistsVar(v) => v.resolve(gamma, target)
      case v@Var(_) => gamma.get(v) match {
        case Some(t) => t.subtype(target) match {
          case None => None
          case Some(t1) => Some(gamma + (v -> t1))
        }
        case None => target match {
          case Some(t1) => Some(gamma + (v -> t1))
          case None => Some(gamma)
        }
      }
      case NoExists(_) => if (BoolType.conformsTo(target)) Some(gamma) else None
      case OnExpiry(_, _, _, _, ty) => if (ty.conformsTo(target)) Some(gamma) else None
      case Named(lft, _) => if (LifetimeType.conformsTo(target)) lft.resolve(gamma, target) else None
      case StaticLifetime => if (LifetimeType.conformsTo(target)) Some(gamma) else None
      case NilLifetime => if (LifetimeType.conformsTo(target)) Some(gamma) else None
      case BoolConst(_) => if (BoolType.conformsTo(target)) Some(gamma) else None
      case LocConst(_) => if (LocType.conformsTo(target)) Some(gamma) else None
      case IntConst(_) => if (IntType.conformsTo(target)) Some(gamma) else None
      case UnaryExpr(op, e) => if (op.outputType.conformsTo(target)) e.resolve(gamma, Some(op.inputType)) else None
      case BinaryExpr(op, l, r) =>
        if (op.resType.conformsTo(target)) {
          for {
            gamma1 <- l.resolve(gamma, Some(op.lType))
            gamma2 <- r.resolve(gamma1, Some(op.rType))
          } yield gamma2
        } else None
      case OverloadedBinaryExpr(overloaded_op, left, right) =>
        val possible_gammas = for{
          ((lTarget, rTarget), op) <- overloaded_op.opFromTypes
          if op.resType.conformsTo(target)
          gamma1 <- left.resolve(gamma, Some(lTarget))
          gamma2 <- right.resolve(gamma1, Some(rTarget))
          is_exactly_defined = (left.getType(gamma2).contains(lTarget)
                            && right.getType(gamma2).contains(rTarget))
        } yield (gamma2, is_exactly_defined)
        val exact_gammas = possible_gammas.filter {case (_, exact) => exact}
        exact_gammas.size match{
          case 0 =>
            possible_gammas.size match{
              case 0 => None
              case 1 => Some(possible_gammas.head._1)
              case _ => BinaryExpr(overloaded_op.default, left, right).resolve(gamma, target) // Ambiguity, using default
            }
          case 1 => Some(exact_gammas.head._1)
          case _ => BinaryExpr(overloaded_op.default, left, right).resolve(gamma, target) // Ambiguity, using default
        }
      case SetLiteral(elems) =>
        if (IntSetType.conformsTo(target)) {
          elems.foldLeft[Option[Gamma]](Some(gamma))((go, e) => go match {
            case None => None
            case Some(g) => e.resolve(g, Some(IntType))
          })
        } else None
      case TupleExpr(exprs) =>
        if (IntType.conformsTo(target)) {
          exprs.foldLeft[Option[Gamma]](Some(gamma))((go, e) => go match {
            case None => None
            case Some(g) => e._1.resolve(g, e._2)
          })
        } else None
      case IfThenElse(c, t, e) =>
        for {
          gamma1 <- c.resolve(gamma, Some(BoolType))
          gamma2 <- t.resolve(gamma1, target)
          t1 = t.getType(gamma2)
          gamma3 <- e.resolve(gamma2, t1)
          t2 = e.getType(gamma3)
          gamma4 <- t2 match {
            case Some(_) => t.resolve(gamma3, t2) // RHS has more information: resolve LHS again
            case None => {
              assert(false, s"ITE with unconstrained types on both sides: $pp")
              None
            }
          }
        } yield gamma4
      case Unknown(_,_,_) => if (BoolType.conformsTo(target)) Some(gamma) else None
    }

    // Expression size in AST nodes
    def size: Int = this match {
      case BinaryExpr(_, l, r) => 1 + l.size + r.size
      case OverloadedBinaryExpr(_, l, r) => 1 + l.size + r.size
      case UnaryExpr(_, arg) => 1 + arg.size
      case SetLiteral(elems) => 1 + elems.map(_.size).sum
      case IfThenElse(cond, l, r) => 1 + cond.size + l.size + r.size
      case _ => 1
    }


    def conjuncts: List[Expr] = this match {
        case BoolConst(true) => Nil
        case BinaryExpr(OpAnd, left, right) => left.conjuncts ++ right.conjuncts
        case OverloadedBinaryExpr(OpAnd, left, right) => left.conjuncts ++ right.conjuncts
        case x => List(x)
    }

    def resolveOverloading(gamma: Gamma): Expr = this match {
      case expr: OverloadedBinaryExpr =>
        BinaryExpr(
          expr.inferConcreteOp(gamma),
          expr.left.resolveOverloading(gamma),
          expr.right.resolveOverloading(gamma)).normalise
      case Var(_)
      | AlwaysExistsVar(_)
      | Named(_, _)
      | OnExpiry(_, _, _, _, _)
      | StaticLifetime
      | NilLifetime
      | BoolConst(_)
      | LocConst(_)
      | IntConst(_)
      | Unknown(_,_,_) => this
      case NoExists(e) => NoExists(e.resolveOverloading(gamma))
      case UnaryExpr(op, e) => UnaryExpr(op, e.resolveOverloading(gamma))
      case BinaryExpr(op, l, r) => BinaryExpr(op, l.resolveOverloading(gamma), r.resolveOverloading(gamma)).normalise
      case SetLiteral(elems) => SetLiteral(elems.map(_.resolveOverloading(gamma)))
      case TupleExpr(exprs) => TupleExpr(exprs.map(tpl => {
          val expr = tpl._1.resolveOverloading(gamma)
          (expr, expr.getType(gamma).orElse(tpl._2))
        }))
      case IfThenElse(c, t, e) => IfThenElse(c.resolveOverloading(gamma),
                                            t.resolveOverloading(gamma),
                                            e.resolveOverloading(gamma)).normalise

    }

    def unifySyntactic(that: Expr, unificationVars: Set[Var]): Option[Subst] = (this, that) match {
      case (_, _)        if this == that                          => Some(Map())
      case (v@Var(_), _) if unificationVars.contains(v)           => Some(Map(v -> that))
      case _ => None
    }

    def normalise: Expr = this
    def flatten: Seq[Expr] = this match {
      case BinaryExpr(OpAnd, l, r) => l.flatten ++ r.flatten
      case _ => Seq(this)
    }
    def isLiteral = this.isInstanceOf[Const] || this.isInstanceOf[SetLiteral]
    def getAlwaysExists: Option[Var] = None
    def isVarLike: Boolean = false
    val evalIntConst: Option[Int] = None
    val evalBoolConst: Option[Boolean] = None
  }

  // Program-level variable: program-level or ghost
  case class Var(name: String) extends Expr {
    override def pp: String = name

    def subst(sigma: Subst): Expr =
      sigma.getOrElse(this, this)

    def varSubst(sigma: Map[Var, Var]): Var = subst(sigma).asInstanceOf[Var]

    def getType(gamma: Gamma): Option[SSLType] = gamma.get(this)
    def isTupleLike: Boolean = name.charAt(0) == '_' && name.substring(1).forall(_.isDigit)
    override def isVarLike: Boolean = true
  }

  case class NoExists(expr: Expr) extends Expr {
    override def pp: String = "#[" + expr.pp + "]"
    override def subst(sigma: Subst): Expr = NoExists(expr.subst(sigma)).normalise
    override def getType(gamma: Gamma): Option[SSLType] = Some(BoolType)
    override def normalise: Expr = expr match {
      case _: Const => BoolConst(true)
      case _ => this
    }
  }
  case class AlwaysExistsVar(v: Var) extends Expr {
    override def pp: String = "(" + v.pp + ")"
    override def subst(sigma: Subst): Expr = if (sigma.contains(v)) v.subst(sigma) else this
    override def getType(gamma: Gamma): Option[SSLType] = v.getType(gamma)
    override def getAlwaysExists: Option[Var] = Some(v)
    override def isVarLike: Boolean = true
  }

  // For existentials (like ^result) post is always None
  // For FA refs post is set when adding it to post (like "^x None" -> "*x Some(true)")
  case class OnExpiry(post: Option[Boolean], futs: List[Boolean], field: Var, idx: Int, ty: SSLType) extends Expr {
    override val pp: String = s"${futsStr("^ ", "* ")}(${ty.pp} ${field.name} $post)[$idx]"
    def futsStr(f: String, c: String): String = futs.reverse.map(if (_) f else c).mkString
    // post is not included in SMT since unifying will make these equal
    val smtName: String = s"ON_EXPIRY_${futsStr("F", "C")}_${field.name}_$idx"
    val asVar: Var = Var(this.pp)
    override def subst(sigma: Subst): Expr = if (sigma.contains(this.asVar)) sigma(this.asVar)
      else if (sigma.contains(field)) OnExpiry(post, futs, sigma(field).asInstanceOf[Var], idx, ty)
      else this
      // In pre (or reborrow)
      // if (sigma.contains(field)) OnExpiry(post, futs, sigma(field).asInstanceOf[Var], idx, ty)
      // In post
      // else
        // sigma.getOrElse(this.asVar, this)

    override def getType(gamma: Gamma): Option[SSLType] = Some(ty)
    override def isVarLike: Boolean = true

    // When FA ref is added to post
    def toPostSub(f: Var, preFnSpec: Seq[Expr], postFnSpec: Seq[Expr]): Option[(Var, Expr)] = if (f == this.field) {
      assert(this.post.isEmpty)
      if (this.futs.forall(!_)) Some(this.asVar -> preFnSpec(idx))
      else if (this.futs.head && this.futs.tail.forall(!_)) Some(this.asVar -> postFnSpec(idx))
      else Some(this.asVar -> this.copy(post = Some(futs.head), futs = false :: futs.tail))
    } else None

    // For a write "*dstF = srcF;" currently only possible in post
    def writeSub(dstF: Var, srcF: Var, fnSpecSrc: Seq[Expr], fnSpecDst: Seq[Expr], inPost: Boolean): Option[(Var, Expr)] = {
      assert(inPost)
      if (dstF == this.field) {
        assert(this.post.isDefined)
        // If this was `^^^x None` then it would become `^^*x Some(true)` and we did:
        // "??; // expire x_rb -> x;" it would become `^^x_rb Some(true)`. At this point we don't
        // want a write "??; *x_rb = tmp; ..." to act on this, but only on `?*x_rb Some(true)`.
        if (this.futs.head == false && this.post.get == inPost) {
          if (futs.length == 1) Some(this.asVar -> fnSpecSrc(this.idx))
          else
            // If we were `^*x_rb Some(true)` then we become `^tmp None` (since tmp is an existential)
            Some(this.asVar -> this.copy(post = None, futs = this.futs.tail, field = srcF))
        // } else if (this.futs.length > 1 && this.futs.head == false && this.futs.tail.head == true && this.post.get == !inPost) {
        //   // If we were `^*x_rb Some(false)` then we become `**tmp Some(true)` (since tmp is an existential)
        //   if (this.futs.tail.tail.forall(!_)) Some(this.asVar -> fnSpecDst(this.idx))
        //   else Some(this.asVar -> this.copy(post = Some(true), futs = false :: false :: this.futs.tail.tail))
        } else None
      } else None
    }

    // For an open "let srcF = &mut **dstF;" or "// expire srcF -> dstF;"
    def openOrExpireSub(dstF: Var, srcF: Var, expire: Boolean): Option[(Var, Expr)] = {
      if (dstF == this.field) {
        assert(this.post.isDefined && this.futs.length > 1)
        // Same reasoning as write
        if (this.futs.head == false && this.post.get == expire) {
          // If we were `^*x Some(true)` then we become `^x_rb Some(true)`
          Some(this.asVar -> this.copy(futs = this.futs.tail, field = srcF))
        } else None
      } else None
    }

    // For an open "let Pred { f, g, ... } = &mut *dstF;" or "// expire { f, g, ... } -> dstF;"
    def openOrExpirePredSub(newFields: Map[Var, Seq[Expr]], expire: Boolean): Option[(Var, Expr)] = {
      // May have substituted in args which are OEs (thus not in newFields map)
      if (!newFields.contains(this.field)) None else {
        // Could have an OE that was obtained from an Open in pre and assigned to arg in post
        // and now the arg has ben subst for a var (we want to ignore such an OE)
        if (this.post.isDefined) None
        // Same reasoning as write
        else if (this.futs.forall(!_)) Some(this.asVar -> newFields(this.field)(idx))
        else Some(this.asVar -> this.copy(post = Some(expire), futs = false :: this.futs))
      }
    }

    // For a read "let v = *f;" currently only possible in pre
    def copyOutSub(f: Var, e: Expr, inPost: Boolean): Option[(Var, Expr)] = {
      assert(!inPost)
      if (f == this.field) {
        assert(this.post.isDefined)
        if (futs.forall(_ == false) && this.post.get == inPost) {
          Some(this.asVar -> e)
        } else None
      } else None
    }

    // For a reborrow "let dstF = &mut *srcF;" currently only possible in post
    def reborrowSub(dstF: Var, srcF: Var, dstFnSpec: Seq[Expr], srcFnSpec: Seq[Expr]): Option[(Var, Expr)] = if (dstF == this.field) {
      assert(this.post.isEmpty)
      if (this.futs.forall(!_))
        Some(this.asVar -> dstFnSpec(idx))
      // Not sound:
      // else if (this.futs.tail.forall(!_))
      //   Some(this.asVar -> srcFnSpec(idx))
      else
        // If we were `?^?tmp None` then we become `?^?x Some(true)`
        // TODO: check that this is sound for e.g. `^^tmp None`
        Some(this.asVar -> this.copy(post = Some(true), field = srcF))
    } else if (srcF == this.field) {
      assert(this.post.isDefined)
      if (this.post.get && this.futs.head == false)
        // If we were `*x Some(true)` then we become `^x Some(true)`
        Some(this.asVar -> this.copy(futs = true :: this.futs.tail))
      else None
    } else None

    // For a reborrow "let dstF = &mut *srcF;" currently only possible from pre
    def reborrowCallSub(dstF: Var, srcF: Var, srcFnSpec: Seq[Expr], newFnSpec: Seq[Expr], vars: Set[Var]): Option[(Var, Expr)] = if (dstF == this.field) {
      val isFut = this.futs.head || (this.post.isDefined && this.post.get)
      if (isFut)
        // If we were `*^arg Some(?)` or `*?arg Some(true)` then its the new value (can subst `None` for `Some(false)`)
        if (this.futs.tail.forall(!_)) Some(this.asVar -> newFnSpec(idx))
        // Otherwise we could be talking about the post `^arg Some(?)` or `?arg Some(true)` (dead in post so doesn't matter if ? is * or ^)
        // If we were `^^arg None` then we become `^*x Some(false)`
        else Some(this.asVar -> this.copy(post = Some(false), field = srcF, futs = false :: this.futs.tail))
      else {
        // Otherwise we could be `**arg Some(false)` (can subst `None` for `Some(false)`)
        if (this.futs.forall(!_)) Some(this.asVar -> srcFnSpec(idx))
        else {
          val v = this.copy(post = Some(false), field = srcF).asVar
          Some(this.asVar -> freshVar(vars, v.name))
        }
      }
    } else if (srcF == this.field) {
      assert(this.post.isDefined)
      if (!this.post.get)
        if (this.futs.forall(!_)) Some(this.asVar -> srcFnSpec(idx))
        else {
          Some(this.asVar -> freshVar(vars, this.asVar.name))
        }
      else None
    } else None
  }

  // Program-level lifetime
  sealed abstract class Lifetime extends Expr {
    def getNamed: Option[NamedLifetime]
    def isNil: Boolean = getNamed.isEmpty
    def subst(sigma: Subst): Lifetime
    override def getType(gamma: Gamma): Option[SSLType] = Some(LifetimeType)
    def rustLft: Option[String] = None
  }
  // Program-level lifetime
  sealed abstract class NamedLifetime extends Lifetime {
    def sig: String
    def isExistential: Boolean = this.getAlwaysExists.isDefined
    override def getNamed: Option[NamedLifetime] = Some(this)
    def getName: Option[Var]
  }
  // Named lifetime, universally quant or exists
  case class Named(name: Var, fa: Boolean) extends NamedLifetime {
    override def pp: String = (if (!fa) "(" else "") + name.pp + (if (!fa) ")" else "")
    override def sig: String = if (this.rustLft.get.startsWith("'_")) "" else this.rustLft.get + " "
    override def subst(sigma: Subst): Lifetime = sigma.get(this.name) match {
      // If Var then its due to a refresh (e.g. when creating companion), pick will also cause this but that shouldn't matter so late
      case Some(e) => if (e.isInstanceOf[Var]) Named(e.asInstanceOf[Var], false) else {
      // All other times it should be here
        assert(!(fa && e == NilLifetime)); e.asInstanceOf[Lifetime]
      }
      case None => this
    }

    override def rustLft: Option[String] = Some("'" + pp.dropRight(2))
    override def getAlwaysExists: Option[Var] = if (!this.fa) Some(name) else None
    override def getName: Option[Var] = Some(this.name)
  }
  case object StaticLifetime extends NamedLifetime {
    override def sig: String = if (this.rustLft.get.startsWith("'_")) "" else this.rustLft.get + " "
    override def subst(sigma: Subst): Lifetime = this
    override def rustLft: Option[String] = Some("'static")
    override def getName: Option[Var] = None
  }
  case object NilLifetime extends Lifetime {
    override def getNamed: Option[NamedLifetime] = None
    override def subst(sigma: Subst): Lifetime = this
  }

  // Program-level constant
  sealed abstract class Const(value: Any) extends Expr {
    override def pp: String = value.toString
    def subst(sigma: Subst): Expr = this
  }

  case class LocConst(value: Integer) extends Const(value) {
    def getType(gamma: Gamma): Option[SSLType] = Some(LocType)
  }

  val NilPtr = LocConst(0)

  case class IntConst(value: Integer) extends Const(value) {
    def getType(gamma: Gamma): Option[SSLType] = Some(IntType)
    override val evalIntConst: Option[Int] = Some(value)
  }

  case class BoolConst(value: Boolean) extends Const(value) {
    def getType(gamma: Gamma): Option[SSLType] = Some(BoolType)
    override val evalBoolConst: Option[Boolean] = Some(value)
  }

  case class BinaryExpr(op: BinOp, left: Expr, right: Expr) extends Expr {
    def subst(sigma: Subst): Expr = BinaryExpr(op, left.subst(sigma), right.subst(sigma)).normalise
    override def normalise: Expr =
      (if (op.isInstanceOf[SymmetricOp] && left.isLiteral && !right.isLiteral) {
        BinaryExpr(op, right, left)
      } else if (this.associative && right.isInstanceOf[BinaryExpr] && right.asInstanceOf[BinaryExpr].op == op) {
        BinaryExpr(op, BinaryExpr(op, left, right.asInstanceOf[BinaryExpr].left), right.asInstanceOf[BinaryExpr].right)
      } else {
        this
      }).simplify

    def simplify: Expr = if (evalIntConst.isDefined) {
        if (evalIntConst.get < 0) UnaryExpr(OpUnaryMinus, IntConst(-evalIntConst.get)) else IntConst(evalIntConst.get)
      } else if (evalBoolConst.isDefined) BoolConst(evalBoolConst.get) else op match {
      case OpLftEq if !(left.isInstanceOf[Lifetime] && right.isInstanceOf[Lifetime]) => ???
      case OpOutlived if !(left.isInstanceOf[Lifetime] && right.isInstanceOf[Lifetime]) => ???
      case OpEq | OpBoolEq | OpLftEq | OpSetEq | OpIntervalEq |
        OpLeq | OpOutlived | OpSubset | OpSubinterval if left == right => BoolConst(true)
      case OpOutlived => (left, right) match {
        case _ if left == right => BoolConst(true)
        case (StaticLifetime, _) => BinaryExpr(OpLftEq, left, right).simplify
        case (_, StaticLifetime) => BoolConst(true)
        case (NilLifetime, _) => BoolConst(true)
        case (_, NilLifetime) => BinaryExpr(OpLftEq, left, right).simplify
        case _ => this
      }
      case OpLftEq if left == right => BoolConst(true)
      case OpLftEq => this
      case OpEq => (left, right) match {
        case (TupleExpr(left), TupleExpr(right)) if left.length == right.length =>
          val both = left.zip(right)
          val gamma = (left ++ right).foldLeft(Map.empty[Var, SSLType])((acc, tpl) => tpl._1.resolve(acc, tpl._2).get)
          both.map(tpl => tpl._1._1 |===| tpl._2._1).fold(BoolConst(true))(_ && _).resolveOverloading(gamma)
        case (e, TupleExpr(_)) if !e.isVarLike => BoolConst(false)
        case (TupleExpr(_), e) if !e.isVarLike => BoolConst(false)
        case (BinaryExpr(OpPlus, left, IntConst(lval)), BinaryExpr(OpPlus, right, IntConst(rval))) =>
          if (lval == rval) BinaryExpr(OpEq, left, right).simplify
          else if (lval < rval) BinaryExpr(OpEq, left, BinaryExpr(OpPlus, IntConst(rval-lval), right)).simplify
          else BinaryExpr(OpEq, BinaryExpr(OpPlus, IntConst(lval-rval), left), right).simplify
        case _ => this
      }
      case OpBoolEq => (left, right) match {
        case (l, BoolConst(true)) => l
        case (BoolConst(true), r) => r
        case _ => this
      }
      case OpMinus => (left, right) match {
        case (_, IntConst(right)) if right == 0 => left
        case (BinaryExpr(OpMinus, ll, IntConst(lr)), IntConst(right)) => BinaryExpr(OpMinus, ll, IntConst(lr+right)).simplify
        case (BinaryExpr(OpPlus, ll, IntConst(lr)), IntConst(right)) =>
          if (lr >= right) BinaryExpr(OpPlus, ll, IntConst(lr-right)).simplify else BinaryExpr(OpMinus, ll, IntConst(right-lr)).simplify
        case _ => this
      }
      case OpPlus => (left, right) match {
        case (_, IntConst(right)) if right == 0 => left
        case (BinaryExpr(OpPlus, ll, IntConst(lr)), IntConst(right)) => BinaryExpr(OpPlus, ll, IntConst(lr+right)).simplify
        case (BinaryExpr(OpMinus, ll, IntConst(lr)), IntConst(right)) =>
          if (lr >= right) BinaryExpr(OpMinus, ll, IntConst(lr-right)).simplify else BinaryExpr(OpPlus, ll, IntConst(right-lr)).simplify
        case _ => this
      }
      case OpAnd => (left, right) match {
        case (BoolConst(true), _) => right
        case (_, BoolConst(true)) => left
        case (BoolConst(false), _) | (_, BoolConst(false)) => BoolConst(false)
        case _ => this
      }
      case OpOr => (left, right) match {
        case (BoolConst(true), _) | (_, BoolConst(true)) => BoolConst(true)
        case (BoolConst(false), _) => right
        case (_, BoolConst(false)) => left
        case _ => this
      }
      case OpField => left match {
        case UnaryExpr(OpTakeRef(_), left) => BinaryExpr(OpField, left, right).normalise
        case UnaryExpr(OpDeRef, left) => BinaryExpr(OpField, left, right).normalise
        case _ => this
      }
      case OpFieldBind if left == right => left
      case _ => this
    }
    override def substUnknown(sigma: UnknownSubst): Expr = BinaryExpr(op, left.substUnknown(sigma), right.substUnknown(sigma))
    override def level: Int = op.level
    override def associative: Boolean = op.isInstanceOf[AssociativeOp]
    override def pp: String = op match {
      case OpRange => printInterval(left, right)
      case _ => s"${left.printInContext(this)}${op.ppSpace}${op.pp}${op.ppSpace}${right.printInContext(this)}"
    }
    def getType(gamma: Gamma): Option[SSLType] = Some(op.resType)

    def printInterval(left: Expr, right: Expr): String = (left, right) match {
      case (IntConst(x), IntConst(y)) if x > y => "[]"
      case _ if left == right => s"[${left.printInContext(this)}]"
      case _ => s"[${left.printInContext(this)} ${op.pp} ${right.printInContext(this)}]"
    }
    override val evalIntConst: Option[Int] = (left.evalIntConst, right.evalIntConst) match {
      case (Some(left), Some(right)) => op match {
        case OpPlus => Some(left + right)
        case OpMinus => Some(left - right)
        case OpMultiply => Some(left * right)
        case _ => None
      }
      case _ => None
    }
    override val evalBoolConst: Option[Boolean] = (left.evalIntConst, right.evalIntConst) match {
      case (Some(left), Some(right)) => op match {
        case OpEq => Some(left == right)
        case OpLeq => Some(left <= right)
        case OpLt => Some(left < right)
        case _ => None
      }
      case _ => (left.evalBoolConst, right.evalBoolConst) match {
        case (Some(left), Some(right)) => op match {
          case OpImplication => Some(!left || right)
          case OpBoolEq => Some(left == right)
          case OpAnd => Some(left && right)
          case OpOr => Some(left || right)
          case _ => None
        }
        case _ => None
      }
    }
  }

  case class OverloadedBinaryExpr(overloaded_op: OverloadedBinOp, left: Expr, right: Expr) extends Expr {
    def subst(sigma: Subst): Expr = OverloadedBinaryExpr(overloaded_op, left.subst(sigma), right.subst(sigma))
    override def substUnknown(sigma: UnknownSubst): Expr = OverloadedBinaryExpr(overloaded_op, left.substUnknown(sigma), right.substUnknown(sigma))
    override def level: Int = overloaded_op.level
    override def associative: Boolean = overloaded_op.isInstanceOf[AssociativeOp]
    override def pp: String = s"${left.printInContext(this)} ${overloaded_op.pp} ${right.printInContext(this)}"

    def inferConcreteOp(gamma: Gamma): BinOp = {
      val lType = left.getType(gamma)
      val rType = right.getType(gamma)
      val strictly_defined_ops = for {
        ((lTarget, rTarget), op) <- overloaded_op.opFromTypes
        if (lType.contains(lTarget)|| lType.isEmpty) && (rType.contains(rTarget) || rType.isEmpty)
      } yield op
      strictly_defined_ops.size match {
        case 1 => strictly_defined_ops.head
        case n if n > 1 =>
          val op = overloaded_op.default
          if (lType.isEmpty || lType.get.conformsTo(Some(op.lType))
            && rType.isEmpty || rType.get.conformsTo(Some(op.rType))) {
            op
          } else {
            throw SynthesisException(s"Operation ${overloaded_op.pp} is ambiguous for strong typing ${(lType, rType)}" +
              s", and arguments don't conform to the default types")
          }
        case 0 =>
          val defined_ops = for {
            ((lTarget, rTarget), op) <- overloaded_op.opFromTypes
            l_ok = lType match {
              case Some(t) => t.conformsTo(Some(lTarget))
              case None => true
            }
            r_ok = rType match {
              case Some(t) => t.conformsTo(Some(rTarget))
              case None => true
            }
            if l_ok && r_ok
          } yield op
          defined_ops.size match {
            case 0 => throw SynthesisException(s"Operation ${overloaded_op.pp} is not defined for input types ${(lType, rType)}")
            case 1 => defined_ops.head
            case _ =>
              val op = overloaded_op.default
              if (lType.isEmpty || lType.get.conformsTo(Some(op.lType))
                && rType.isEmpty || rType.get.conformsTo(Some(op.rType))) {
                op
              } else {
                throw SynthesisException(s"Operation ${overloaded_op.pp} is ambiguous for weak typing ${(lType, rType)}" +
                  s", and arguments don't conform to the default types")
              }
          }
      }
    }
    override def getType(gamma: Gamma): Option[SSLType] = Some(inferConcreteOp(gamma).resType)
  }

  case class UnaryExpr(op: UnOp, arg: Expr) extends Expr {
    def subst(sigma: Subst): Expr = UnaryExpr(op, arg.subst(sigma)).normalise
    override def normalise: Expr = if (evalIntConst.isDefined) {
        if (evalIntConst.get < 0) UnaryExpr(OpUnaryMinus, IntConst(-evalIntConst.get)) else IntConst(evalIntConst.get)
      } else if (evalBoolConst.isDefined) BoolConst(evalBoolConst.get) else (op, arg) match {
      case (OpDeRef, UnaryExpr(OpTakeRef(_), arg)) => arg.normalise
      case (OpNot, UnaryExpr(OpNot, arg)) => arg.normalise
      case (OpUnaryMinus, UnaryExpr(OpUnaryMinus, arg)) => arg.normalise
      case _ => this
    }
    override def substUnknown(sigma: UnknownSubst): Expr = UnaryExpr(op, arg.substUnknown(sigma))
    override def level = op.level
    override def associative: Boolean = op.isInstanceOf[AssociativeOp]
    override def pp: String =
      if (op.postfix) s"${arg.printInContext(this)}${op.pp}"
      else s"${op.pp}${arg.printInContext(this)}"
    def getType(gamma: Gamma): Option[SSLType] = Some(op.outputType)
    override val evalIntConst: Option[Int] = (op, arg.evalIntConst) match {
      case (OpUnaryMinus, Some(arg)) => Some(-arg)
      case _ => None
    }
    override val evalBoolConst: Option[Boolean] = (op, arg.evalBoolConst) match {
      case (OpNot, Some(arg)) => Some(!arg)
      case _ => None
    }
  }

  case class SetLiteral(elems: List[Expr]) extends Expr {
    override def pp: String = s"{${elems.map(_.pp).mkString(", ")}}"
    override def subst(sigma: Subst): SetLiteral = SetLiteral(elems.map(_.subst(sigma)))
    def getType(gamma: Gamma): Option[SSLType] = Some(IntSetType)
  }

  case class TupleExpr(exprs: List[(Expr, Option[SSLType])]) extends Expr {
    override def pp: String = s"(${exprs.map(_._1.pp).mkString(", ")})"
    override def subst(sigma: Subst): TupleExpr = TupleExpr(exprs.map(e => (e._1.subst(sigma), e._2)))
    def getType(gamma: Gamma): Option[SSLType] = Some(IntType)
  }

  case class IfThenElse(cond: Expr, left: Expr, right: Expr) extends Expr {
    override def level: Int = 0
    override def pp: String = s"${cond.printInContext(this)} ? ${left.printInContext(this)} : ${right.printInContext(this)}"
    override def subst(sigma: Subst): Expr = IfThenElse(cond.subst(sigma), left.subst(sigma), right.subst(sigma)).normalise
    override def normalise: Expr = (cond.evalBoolConst, left.evalBoolConst, right.evalBoolConst) match {
      case (Some(true), _, _) => left
      case (Some(false), _, _) => right
      case (_, Some(false), _) => (cond.not && right).normalise
      case (_, _, Some(false)) => (cond && left).normalise
      case _ => this
    }
    override def substUnknown(sigma: UnknownSubst): Expr = IfThenElse(cond.substUnknown(sigma), left.substUnknown(sigma), right.substUnknown(sigma))
    def getType(gamma: Gamma): Option[SSLType] = left.getType(gamma)
  }

  /**
    * Unknown predicate (to be replaced by a term)
    * @param name Predicate name
    * @param params Variables that may appear in the instantiation
    */
  case class Unknown(name: String, params: Set[Var], pendingSubst: Subst = Map()) extends Expr with PureLogicUtils {
    override def getType(gamma: Gamma): Option[SSLType] = Some(BoolType)

    override def pp: String = s"?$name(${params.map(_.name).mkString(", ")})"

    override def subst(sigma: Subst): Expr = this.copy(pendingSubst = compose(this.pendingSubst, sigma))

    // Compare ignoring the pending substitution
    def sameVar(other: Unknown): Boolean = other.name == name && other.params == params

    override def substUnknown(sigma: UnknownSubst): Expr =
      // Find unknown but ignore pending subst
      sigma.find({case (k, _) => sameVar(k)}) match {
      case None => this
      case Some((_,e)) => e.subst(pendingSubst)
    }
  }

  /*
  Common expressions
   */

  def eTrue: Expr = BoolConst(true)
  def eFalse: Expr = BoolConst(false)
  def emptyInt: Expr = BinaryExpr(OpRange, IntConst(1), IntConst(0))

  /*
  Substitutions
   */
  type Subst = Map[Var, Expr]
  type SubstVar = Map[Var, Var]
  type ExprSubst = Map[Expr, Expr]
  type UnknownSubst = Map[Unknown, Expr]

  def toSorted[A <: Expr](s: Set[A]): List[A] = s.toList.sorted(Ordering[Expr])
  def least[A <: Expr](s: Set[Var]): List[Var] = if (s.isEmpty) Nil else List(s.min(Ordering[Expr]))

}





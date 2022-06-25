package org.tygus.suslik.language

import org.tygus.suslik.logic.{Gamma, PureLogicUtils}
import org.tygus.suslik.synthesis.SynthesisException

/**
  * @author Ilya Sergey
  */

object Expressions {

  sealed abstract class UnOp extends PrettyPrinting {
    def inputType: SSLType
    def outputType: SSLType
  }
  object OpNot extends UnOp {
    override def pp: String = "not"
    override def inputType: SSLType = BoolType
    override def outputType: SSLType = BoolType
  }

  object OpUnaryMinus extends UnOp {
    override def pp: String = "-"
    override def inputType: SSLType = IntType
    override def outputType: SSLType = IntType
  }

  object OpLower extends UnOp {
    override def pp: String = "lower"
    override def inputType: SSLType = IntervalType
    override def outputType: SSLType = IntType
  }

  object OpUpper extends UnOp {
    override def pp: String = "upper"
    override def inputType: SSLType = IntervalType
    override def outputType: SSLType = IntType
  }

  case class OpTakeRef(mut: Boolean) extends UnOp {
    override def pp: String = if (mut) "&mut" else "&"
    override def inputType: SSLType = LocType
    override def outputType: SSLType = LocType
  }
  object OpDeRef extends UnOp {
    override def pp: String = "*"
    override def inputType: SSLType = LocType
    override def outputType: SSLType = LocType
  }

  sealed abstract class BinOp extends OverloadedBinOp {
    def lType:SSLType
    def rType: SSLType

    override def opFromTypes: Map[(SSLType, SSLType), BinOp] = Map((lType, rType) -> this)

    override def default: BinOp = this

    def resType: SSLType
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
      (LifetimeType, LifetimeType) -> OpOutlives,
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
  object OpOutlives extends RelOp {
    def level: Int = 3
    override def pp: String = "<="
    def lType: SSLType = LifetimeType
    def rType: SSLType = LifetimeType
  }
  object OpField extends BinOp {
    def level: Int = 4
    override def pp: String = "."
    def lType: SSLType = LocType
    def rType: SSLType = LocType
    override def resType: SSLType = LocType
  }


  sealed abstract class Expr extends PrettyPrinting with HasExpressions[Expr] with Ordered[Expr] {

    def compare(that: Expr): Int = this.pp.compare(that.pp)

    // Type-coercing visitor (yikes!)
    def collect[R <: Expr](p: Expr => Boolean): Set[R] = {

      def collector(acc: Set[R])(exp: Expr): Set[R] = exp match {
        case v@Var(_) if p(v) => acc + v.asInstanceOf[R]
        case n@Named(v) => {
          val acc1 = if (p(n)) acc + n.asInstanceOf[R] else acc
          collector(acc1)(v)
        }
        case NilLifetime if p(NilLifetime) => acc + NilLifetime.asInstanceOf[R]
        case c@IntConst(_) if p(c) => acc + c.asInstanceOf[R]
        case c@LocConst(_) if p(c) => acc + c.asInstanceOf[R]
        case c@BoolConst(_) if p(c) => acc + c.asInstanceOf[R]
        case b@BinaryExpr(_, l, r) =>
          val acc1 = if (p(b)) acc + b.asInstanceOf[R] else acc
          val acc2 = collector(acc1)(l)
          collector(acc2)(r)
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

    def level: Int = 6
    def associative: Boolean = false

    def printInContext(parent: Expr): String = {
      val s = pp
      if (parent.level < this.level) s
      else this match {
        case expr: BinaryExpr if associative && parent.isInstanceOf[BinaryExpr] && expr.op == parent.asInstanceOf[BinaryExpr].op => s
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
      case v@Var(_) => (if (v.name.endsWith("_FA")) gamma.get(Var(v.name.dropRight(3))) else gamma.get(v)) match {
        case Some(t) => t.subtype(target) match {
          case None => None
          case Some(t1) => Some(gamma + (v -> t1))
        }
        case None => target match {
          case Some(t1) => Some(gamma + (v -> t1))
          case None => Some(gamma)
        }
      }
      case Named(lft) => if (LifetimeType.conformsTo(target)) lft.resolve(gamma, target) else None
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
      | Named(_)
      | NilLifetime
      | BoolConst(_)
      | LocConst(_)
      | IntConst(_)
      | Unknown(_,_,_) => this
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
  }

  // Program-level variable: program-level or ghost
  case class Var(name: String) extends Expr {
    override def pp: String = name

    def subst(sigma: Subst): Expr =
      sigma.getOrElse(this, this)

    def varSubst(sigma: Map[Var, Var]): Var = subst(sigma).asInstanceOf[Var]

    def getType(gamma: Gamma): Option[SSLType] = gamma.get(this)
  }

  // Program-level lifetime
  sealed abstract class Lifetime extends Expr {
    def getNamed: Option[Named]
    def isNil: Boolean = getNamed.isEmpty
    def subst(sigma: Subst): Lifetime
    override def getType(gamma: Gamma): Option[SSLType] = Some(LifetimeType)
    def rustLft: Option[String] = None
  }
  // Program-level variable: program-level or ghost
  case class Named(name: Var) extends Lifetime {
    override def pp: String = name.pp

    override def getNamed: Option[Named] = Some(this)
    override def subst(sigma: Subst): Lifetime = sigma.get(this.name) match {
      case Some(NilLifetime) => NilLifetime
      case Some(IntConst(i)) if i == 0 => NilLifetime
      case Some(e) => Named(e.asInstanceOf[Var])
      case None => this
    }
      
    override def rustLft: Option[String] = Some("'" + pp.dropRight(2))
    
    def refresh(field: String): Named = Named(Var(field + "_" + name.name))
  }
  case object NilLifetime extends Lifetime {
    override def getNamed: Option[Named] = None
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
  }

  case class BoolConst(value: Boolean) extends Const(value) {
    def getType(gamma: Gamma): Option[SSLType] = Some(BoolType)
  }

  case class BinaryExpr(op: BinOp, left: Expr, right: Expr) extends Expr {
    def subst(sigma: Subst): Expr = BinaryExpr(op, left.subst(sigma), right.subst(sigma)).normalise
    override def normalise: Expr =
      (if (op.isInstanceOf[SymmetricOp] && left.isInstanceOf[Const] && !right.isInstanceOf[Const]) {
        BinaryExpr(op, right, left)
      } else if (op.isInstanceOf[AssociativeOp] && right.isInstanceOf[BinaryExpr] && right.asInstanceOf[BinaryExpr].op == op) {
        BinaryExpr(op, BinaryExpr(op, left, right.asInstanceOf[BinaryExpr].left), right.asInstanceOf[BinaryExpr].right)
      } else {
        this
      }).simplify

    def simplify: Expr = op match {
      case OpEq | OpBoolEq | OpLftEq if left == right => BoolConst(true)
      case OpEq => (left, right) match {
        case (IntConst(left), IntConst(right)) if left != right => BoolConst(false)
        case (TupleExpr(left), TupleExpr(right)) if left.length != right.length => BoolConst(false)
        case (TupleExpr(left), TupleExpr(right)) =>
          val both = left.zip(right)
          val gamma = (left ++ right).foldLeft(Map.empty[Var, SSLType])((acc, tpl) => tpl._1.resolve(acc, tpl._2).get)
          both.map(tpl => tpl._1._1 |===| tpl._2._1).fold(BoolConst(true))(_ && _).resolveOverloading(gamma)
        case (BinaryExpr(OpPlus, left, IntConst(lval)), BinaryExpr(OpPlus, right, IntConst(rval))) =>
          if (lval == rval) BinaryExpr(OpEq, left, right).simplify
          else if (lval < rval) BinaryExpr(OpEq, left, BinaryExpr(OpPlus, IntConst(rval-lval), right)).simplify
          else BinaryExpr(OpEq, BinaryExpr(OpPlus, IntConst(lval-rval), left), right).simplify
        case _ => this
      }
      case OpBoolEq => (left, right) match {
        case (BoolConst(left), BoolConst(right)) if left != right => BoolConst(false)
        case _ => this
      }
      case OpLeq | OpLt => (left, right) match {
        case (IntConst(left), IntConst(right)) => {
          if (left < right || (left == right && op == OpLeq)) BoolConst(true)
          else BoolConst(false)
        }
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
        case _ => this
      }
      case _ => this
    }
    override def substUnknown(sigma: UnknownSubst): Expr = BinaryExpr(op, left.substUnknown(sigma), right.substUnknown(sigma))
    override def level: Int = op.level
    override def associative: Boolean = op.isInstanceOf[AssociativeOp]
    override def pp: String = op match {
      case OpRange => printInterval(left, right)
      case _ => s"${left.printInContext(this)} ${op.pp} ${right.printInContext(this)}"
    }
    def getType(gamma: Gamma): Option[SSLType] = Some(op.resType)

    def printInterval(left: Expr, right: Expr): String = (left, right) match {
      case (IntConst(x), IntConst(y)) if x > y => "[]"
      case _ if left == right => s"[${left.printInContext(this)}]"
      case _ => s"[${left.printInContext(this)} ${op.pp} ${right.printInContext(this)}]"
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
    override def normalise: Expr = (op, arg) match {
      case (OpDeRef, UnaryExpr(OpTakeRef(_), arg)) => arg.normalise
      case _ => this
    }
    override def substUnknown(sigma: UnknownSubst): Expr = UnaryExpr(op, arg.substUnknown(sigma))
    override def level = 5
    override def pp: String = s"${op.pp} ${arg.printInContext(this)}"
    def getType(gamma: Gamma): Option[SSLType] = Some(op.outputType)
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
    override def normalise: Expr = (cond, left, right) match {
      case (BoolConst(true), _, _) => left
      case (BoolConst(false), _, _) => right
      case (_, BoolConst(false), _) => (cond.not && right).normalise
      case (_, _, BoolConst(false)) => (cond && left).normalise
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





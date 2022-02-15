package org.tygus.suslik.logic

import org.tygus.suslik.language.Expressions.Permissions._
import org.tygus.suslik.language.Expressions._
import org.tygus.suslik.language._
import org.tygus.suslik.synthesis.SynthesisException

/**
  * Separation logic fragment
  */
sealed abstract class Heaplet extends PrettyPrinting with HasExpressions[Heaplet] with Ordered[Heaplet] with SepLogicUtils {

  // Collect certain sub-expressions
  def collect[R <: Expr](p: Expr => Boolean): Set[R] = {
    def collector(acc: Set[R])(h: Heaplet): Set[R] = h match {
      case PointsTo(v, _, value, perm) =>
        acc ++ v.collect(p) ++ value.collect(p) ++ perm.collect(p)
      case Block(v, _, perm) =>
        acc ++ v.collect(p) ++ perm.collect(p)
      case SApp(_, args, _, card) =>
        args.foldLeft(acc)((a, e) => a ++ e.collect(p)) ++
          // [Cardinality] add the cardinality variable
          card.collect(p)
    }

    collector(Set.empty)(this)
  }

  // Unify with that modulo theories:
  // produce pairs of expressions that must be equal for the this and that to be the same heaplet
  def unify(that: Heaplet): Option[ExprSubst]

  def compare(that: Heaplet): Int = this.pp.compare(that.pp)

  def resolve(gamma: Gamma, env: Environment): Option[Gamma]

  def getTag: Option[PTag] = None

  def setTag(t: PTag): Heaplet = this

  def eqModTags(other: Heaplet): Boolean = {
    this.setTag(PTag()) == other.setTag(PTag())
  }

  // If this is a predicate instance, assume that from is too and copy its tag
  def copyTag(from: Heaplet): Heaplet = this match {
    case SApp(pred, args, _, card) => SApp(pred, args, from.asInstanceOf[SApp].tag, card)
    case _ => this
  }

  // Size of the heaplet (in AST nodes)
  def size: Int = this match {
    case PointsTo(loc, _, value, _) => 1 + loc.size + value.size
    case Block(loc, _, _) => 1 + loc.size
    case SApp(_, args, _, _) => args.map(_.size).sum
  }

  def cost: Int = this match {
    case SApp(_, _, PTag(c, u), _) => 2 + 2*(c + u)
    case _ => 1
  }
  
  protected def ppPermWithDefault(perm: Expr): String  = perm match {
    case PermConst(Mutable) => ""
    case _ => s"@${perm.pp}"
  }
}

/**
  * var + offset :-> value
  */
case class PointsTo(loc: Expr, offset: Int = 0, value: Expr, perm: Expr = eMut) extends Heaplet {

  override def resolveOverloading(gamma: Gamma): Heaplet =
    this.copy(loc = loc.resolveOverloading(gamma), value = value.resolveOverloading(gamma), perm = perm.resolveOverloading(gamma))

  override def pp: Ident = {
    val head = if (offset <= 0) loc.pp else s"(${loc.pp} + $offset)"
    s"$head :->${ppPermWithDefault(perm)} ${value.pp}"
  }

  def subst(sigma: Map[Var, Expr]): Heaplet = loc.subst(sigma) match {
    case BinaryExpr(OpPlus, l, IntConst(off)) => PointsTo(l, offset + off, value.subst (sigma), perm.subst(sigma))
    case _ => PointsTo (loc.subst (sigma), offset, value.subst (sigma), perm.subst(sigma))
  }

  def resolve(gamma: Gamma, env: Environment): Option[Gamma] = {
    for {
      gamma1 <- loc.resolve(gamma, Some(LocType))
      gamma2 <- value.resolve(gamma1, Some(LocType))
      gamma3 <- perm.resolve(gamma2, Some(PermType))
    } yield gamma3
  }

  override def compare(that: Heaplet) = that match {
    case SApp(pred, args, tag, card) => -1
    case _ => super.compare(that)
  }

  // This only unifies the rhs of the points-to, because lhss are unified by a separate rule
  override def unify(that: Heaplet): Option[ExprSubst] = that match {
    case PointsTo(l, o, v, p) if l == loc && o == offset => Some(Map(value -> v, perm -> p))
    case _ => None
  }
}

/**
  * LABEL@(type) :-> value
  */
case class Label(loc: Expr, tp: Ident, value: Expr, perm: Expr = eMut) extends Heaplet {

  override def resolveOverloading(gamma: Gamma): Heaplet =
    this.copy(loc = loc.resolveOverloading(gamma), value = value.resolveOverloading(gamma), perm = perm.resolveOverloading(gamma))

  override def pp: Ident = {
    s"${loc.pp}@($tp) :->${ppPermWithDefault(perm)} ${value.pp}"
  }

  def subst(sigma: Map[Var, Expr]): Heaplet = loc.subst(sigma) match {
    //case BinaryExpr(OpPlus, l, IntConst(off)) => Label(l, offset + off, value.subst (sigma), perm.subst(sigma))
    case _ => Label(loc.subst(sigma), tp, value.subst(sigma), perm.subst(sigma))
  }

  def resolve(gamma: Gamma, env: Environment): Option[Gamma] = {
    for {
      gamma1 <- loc.resolve(gamma, Some(LocType))
      gamma2 <- value.resolve(gamma1, Some(LocType))
      gamma3 <- perm.resolve(gamma2, Some(PermType))
    } yield gamma3
  }

  override def compare(that: Heaplet) = that match {
    case SApp(pred, args, tag, card) => -1
    case _ => super.compare(that)
  }

  // This only unifies the rhs of the points-to, because lhss are unified by a separate rule
  override def unify(that: Heaplet): Option[ExprSubst] = that match {
    case Label(l, t, v, p) if l == loc && t == tp => Some(Map(value -> v, perm -> p))
    case _ => None
  }
}

/**
  * block(var, size)
  */
case class Block(loc: Expr, sz: Int, perm: Expr = eMut) extends Heaplet {

  override def resolveOverloading(gamma: Gamma): Heaplet = this.copy(loc = loc.resolveOverloading(gamma))

  override def pp: Ident = {
    s"[${loc.pp}, $sz]${ppPermWithDefault(perm)}"
  }

  def subst(sigma: Map[Var, Expr]): Heaplet = {
    Block(loc.subst(sigma), sz, perm.subst(sigma))
  }

  def resolve(gamma: Gamma, env: Environment): Option[Gamma] = {
    for {
      gamma1 <- loc.resolve(gamma, Some(LocType))
      gamma2 <- perm.resolve(gamma1, Some(PermType))
    } yield gamma2
  }

  override def compare(that: Heaplet) = that match {
    case SApp(pred, args, tag, card) => -1
    case _ => super.compare(that)
  }

  override def unify(that: Heaplet): Option[ExprSubst] = that match {
    case Block(l, s, p) if sz == s => Some(Map(loc -> l, perm -> p))
    case _ => None
  }
}

case class PTag(calls: Int = 0, unrolls: Int = 0) extends PrettyPrinting {
  override def pp: String = this match {
    case PTag(0, 0) => "" // Default tag
    case _ => s"[$calls,$unrolls]"
  }
}

/**
  *
  * @card is a cardinality of a current call.
  *
  *       Predicate application
  */
case class SApp(pred: Ident, args: Seq[Expr], tag: PTag, card: Expr) extends Heaplet {

  override def resolveOverloading(gamma: Gamma): Heaplet = this.copy(args = args.map(_.resolveOverloading(gamma)))

  override def pp: String = {
    def ppCard(e: Expr) = s"<${e.pp}>"

    s"$pred(${args.map(_.pp).mkString(", ")})${ppCard(card)}${tag.pp}"
  }


  override def compare(that: Heaplet): Int = that match {
    case SApp(pred1, args1, tag, card) =>
      val c1 = this.pred.compareTo(pred1)
      val c2 = this.args.toString.compareTo(args1.toString)
      if (c1 != 0) return c1
      if (c2 != 0) return c2
      0
    case _ => super.compare(that)
  }

  def subst(sigma: Map[Var, Expr]): Heaplet = {
    val newArgs = args.map(_.subst(sigma))
    // [Cardinality] adjust cardinality
    val newCard = card.subst(sigma)
    this.copy(args = newArgs, card = newCard)
  }

  def resolve(gamma: Gamma, env: Environment): Option[Gamma] = {
    if (!(env.predicates contains pred)) {
      throw SynthesisException(s"predicate $pred is undefined")
    }

    val gamma1 = card.resolve(gamma, Some(CardType))
    val formals = env.predicates(pred).params
    if (formals.length == args.length) {
      (formals, args).zipped.foldLeft[Option[Gamma]](gamma1) { case (go, (formal, actual)) => go match {
        case None => None
        case Some(g) => actual.resolve(g, Some(formal._2))
      }
      }
    } else None
  }

  override def getTag: Option[PTag] = Some(tag)

  override def setTag(t: PTag): Heaplet = this.copy(tag = t)

  override def unify(that: Heaplet): Option[ExprSubst] = that match {
    case SApp(p, as, _, c) if pred == p => Some((card :: args.toList).zip(c :: as.toList).toMap)
    case _ => None
  }
}


case class SFormula(chunks: List[Heaplet], typemap: Map[Var, Option[Any]]) extends PrettyPrinting with HasExpressions[SFormula] {
  def resolveOverloading(gamma: Gamma): SFormula = {
    this.copy(chunks = chunks.map(_.resolveOverloading(gamma)))
  }

  override def pp: Ident = if (chunks.isEmpty) "emp" else {
    def pt(l: List[Heaplet]) = l.map(_.pp).sortBy(x => x)

    List(ptss, apps, blocks).flatMap(pt).mkString(" ** ")
  }

  def blocks: List[Block] = for (b@Block(_, _, _) <- chunks) yield b

  def apps: List[SApp] = for (b@SApp(_, _, _, _) <- chunks) yield b

  def ptss: List[PointsTo] = for (b@PointsTo(_, _, _, _) <- chunks) yield b

  def subst(sigma: Map[Var, Expr]): SFormula = SFormula(chunks.map(_.subst(sigma)), typemap.map { case (v, ty) => sigma(v).asInstanceOf[Var] -> ty })

  // Collect certain sub-expressions
  def collect[R <: Expr](p: Expr => Boolean): Set[R] = {
    chunks.foldLeft(Set.empty[R])((a, h) => a ++ h.collect(p))
  }

  def setSAppTags(t: PTag): SFormula = SFormula(chunks.map(h => h.setTag(t)), typemap)

  def callTags: List[Int] = chunks.flatMap(_.getTag).map(_.calls)

  def isEmp: Boolean = chunks.isEmpty

  def block_size (expr: Expr) = blocks find { case Block(loc,_,_) if loc == expr => true case _ => false } map (v => v.sz)

  // Add h to chunks (multiset semantics)
  def **(h: Heaplet): SFormula = SFormula(h :: chunks, typemap)

  // Add all chunks from other (multiset semantics)
  def **(other: SFormula): SFormula = SFormula(chunks ++ other.chunks, (typemap.toSeq ++ other.typemap.toSeq).toMap)

  // Remove h from this formula (multiset semantics)
  def -(h: Heaplet): SFormula = SFormula(chunks.diff(List(h)), typemap)

  // Remove all chunks present in other (multiset semantics)
  def -(other: SFormula): SFormula = SFormula(chunks.diff(other.chunks), typemap.toSeq.diff(other.typemap.toSeq).toMap)

  // Add chunks from other (set semantics)
  def +(other: SFormula): SFormula = SFormula((chunks ++ other.chunks).distinct, (typemap.toSeq ++ other.typemap.toSeq).toMap)

  def disjoint(other: SFormula): Boolean = chunks.intersect(other.chunks).isEmpty

  def resolve(gamma: Gamma, env: Environment): Option[Gamma] = {
    chunks.foldLeft[Option[Map[Var, SSLType]]](Some(gamma))((go, h) => go match {
      case None => None
      case Some(g) => h.resolve(g, env)
    })
  }

  def replace(what: SFormula, replacement: SFormula): SFormula = {
    (this - what) ** replacement
  }

  lazy val profile: SProfile = {
    val appProfile = apps.groupBy(_.pred).mapValues(_.length)
    val blockProfile = blocks.groupBy(_.sz).mapValues(_.length)
    val ptsProfile = ptss.groupBy(_.offset).mapValues(_.length)
    SProfile(appProfile, blockProfile, ptsProfile)
  }


  // Size of the formula (in AST nodes)
  def size: Int = chunks.map(_.size).sum

  def cost: Int = chunks.map(_.cost).sum

  //  def cost: Int = chunks.foldLeft(0)((m, c) => m.max(c.cost))
  def resolve_pts_types() = {
    /*
    var type_map: Map[Expr, Any] = apps.map(app => app.args(0) -> app.pred).toMap
    var ptss_list = ptss
    var old_len = ptss_list.length + 1
    while (ptss_list.length != old_len) {
      old_len = ptss_list.length
      ptss_list = ptss_list.filter(pts => pts.value match {
        case v@Var(_) => type_map.get(v) match {
          case p@Some(tp) => {
            pts.tp = p
            if (pts.offset == 0) {
              type_map = type_map + (pts.loc -> (pts.perm, tp))
            }
            false
          }
          case None => true
        }
        case LocConst(value) => false
        case IntConst(value) => {
          pts.tp = Some("int")
          false
        }
        case BoolConst(value) => {
          pts.tp = Some("bool")
          false
        }
        case PermConst(value) => false
        case BinaryExpr(op, left, right) => {
          pts.tp = Some(op.resType.pp)
          false
        }
        case OverloadedBinaryExpr(overloaded_op, left, right) => ???
        case UnaryExpr(op, arg) => {
          pts.tp = Some(op.outputType.pp)
          false
        }
        case SetLiteral(elems) => ???
        case IfThenElse(cond, left, right) => ???
        case Unknown(name, params, pendingSubst) => ???
      })
    }
    */
  }
}

/**
  * Profile of a spatial formula (contains properties that cannot be changed by unification)
  * @param apps how maybe applications there are of each predicate?
  * @param blocks how many blocks there are of each size?
  * @param ptss how many points-to chunks there are with each offset?
  */
case class SProfile(apps: Map[Ident, Int], blocks: Map[Int, Int], ptss: Map[Int, Int])



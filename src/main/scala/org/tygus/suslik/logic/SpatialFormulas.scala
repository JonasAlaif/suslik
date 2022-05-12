package org.tygus.suslik.logic

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
      case PointsTo(v, offset, value) =>
        val acc1 = if (p(v)) acc + v.asInstanceOf[R] else acc
        acc1 ++ value.collect(p)
      case Block(v, _) =>
        if (p(v)) acc + v.asInstanceOf[R] else acc
      case SApp(_, args, _, card) =>
        args.foldLeft(acc)((a, e) => a ++ e.collect(p)) ++
          // [Cardinality] add the cardinality variable
          card.collect(p)
      case RApp(_, field, ref, _, fnSpec, lft, _) =>
        field.collect(p) ++ ref.map(_.lft.collect(p)).getOrElse(Set.empty) ++
          fnSpec.foldLeft(acc)((a, e) => a ++ e.collect(p)) ++ lft.collect(p)
    }

    collector(Set.empty)(this)
  }

  // Unify with that modulo theories:
  // produce pairs of expressions that must be equal for the this and that to be the same heaplet
  def unify(that: Heaplet): Option[ExprSubst]

  // Unify syntactically: find a subst for existentials in this
  // that makes it syntactically equal to that
  def unifySyntactic(that: Heaplet, unificationVars: Set[Var]): Option[Subst]

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
    case PointsTo(loc, _, value) => 1 + loc.size + value.size
    case Block(loc, _) => 1 + loc.size
    case SApp(_, args, _, _) => args.map(_.size).sum
    case RApp(_, _, _, _, fnSpec, _, _) => 1 + fnSpec.map(_.size).sum
  }

  def cost: Int = this match {
    case SApp(_, _, PTag(c, u), _) => 2 + 2*(c + u)
    case RApp(_, _, _, _, _, _, PTag(c, u)) => 2 + 2*(c + u)
    case _ => 1
  }

}

/**
  * var + offset :-> value
  */
case class PointsTo(loc: Expr, offset: Int = 0, value: Expr) extends Heaplet {

  override def resolveOverloading(gamma: Gamma): Heaplet =
    this.copy(loc = loc.resolveOverloading(gamma), value = value.resolveOverloading(gamma))

  override def pp: Ident = {
    val head = if (offset <= 0) loc.pp else s"(${loc.pp} + $offset)"
    s"$head :-> ${value.pp}"
  }

  def subst(sigma: Map[Var, Expr]): Heaplet = loc.subst(sigma) match {
    case BinaryExpr(OpPlus, l, IntConst(off)) => PointsTo(l, offset + off, value.subst (sigma))
    case _ => PointsTo (loc.subst (sigma), offset, value.subst (sigma) )
  }

  def resolve(gamma: Gamma, env: Environment): Option[Gamma] = {
    for {
      gamma1 <- loc.resolve(gamma, Some(LocType))
      gamma2 <- value.resolve(gamma1, Some(LocType))
    } yield gamma2
  }

  override def compare(that: Heaplet) = that match {
    case SApp(pred, args, tag, card) => -1
    case _ => super.compare(that)
  }

  // This only unifies the rhs of the points-to, because lhss are unified by a separate rule
  override def unify(that: Heaplet): Option[ExprSubst] = that match {
    case PointsTo(l, o, v) if l == loc && o == offset => Some(Map(value -> v))
    case _ => None
  }

  override def unifySyntactic(that: Heaplet, unificationVars: Set[Var]): Option[Subst] = that match {
    case PointsTo(l, o, v) if o == offset =>
      for {
        sub1 <- loc.unifySyntactic(l, unificationVars)
        sub2 <- value.subst(sub1).unifySyntactic(v.subst(sub1), unificationVars)
      } yield sub1 ++ sub2
    case _ => None
  }
}

/**
  * block(var, size)
  */
case class Block(loc: Expr, sz: Int) extends Heaplet {

  override def resolveOverloading(gamma: Gamma): Heaplet = this.copy(loc = loc.resolveOverloading(gamma))

  override def pp: Ident = {
    s"[${loc.pp}, $sz]"
  }

  def subst(sigma: Map[Var, Expr]): Heaplet = {
    Block(loc.subst(sigma), sz)
  }

  def resolve(gamma: Gamma, env: Environment): Option[Gamma] = loc.resolve(gamma, Some(LocType))

  override def compare(that: Heaplet) = that match {
    case SApp(pred, args, tag, card) => -1
    case _ => super.compare(that)
  }

  override def unify(that: Heaplet): Option[ExprSubst] = that match {
    case Block(l, s) if sz == s => Some(Map(loc -> l))
    case _ => None
  }

  override def unifySyntactic(that: Heaplet, unificationVars: Set[Var]): Option[Subst] = that match {
    case Block(l, s) if sz == s => loc.unifySyntactic(l, unificationVars)
    case _ => None
  }
}

case class PTag(calls: Int = 0, unrolls: Int = 0) extends PrettyPrinting {
  override def pp: String = this match {
    case PTag(0, 0) => "" // Default tag
    case _ => s"[$calls,$unrolls]"
  }
  def incrUnrolls: PTag = this.copy(unrolls = unrolls+1)
  def incrCalls: PTag = this.copy(calls = calls+1)
}

/**
  *
  * @param card is a cardinality of a current call.
  *
  *       Predicate application
  */
case class SApp(pred_with_info: Ident, args: Seq[Expr], tag: PTag, card: Expr) extends Heaplet {
  // Must be unfolded/reborrowed immediately
  def isGhost = pred_with_info.endsWith("_GHOST")
  // Use Open/Close or Reborrow
  def isBorrow = pred_with_info.startsWith("BRRW_")
  // Must be unfolded immediately
  def isPrim = pred_with_info.startsWith("PRIM_")
  // Ident to locate predicate from env
  def pred_no_ghost: Ident = if (isGhost) pred_with_info.dropRight(6) else pred_with_info
  def pred: Ident = if (isBorrow) pred_no_ghost.drop(5) else pred_no_ghost

  override def resolveOverloading(gamma: Gamma): Heaplet = this.copy(args = args.map(_.resolveOverloading(gamma)))

  override def pp: String = {
    def ppCard(e: Expr) = s"<${e.pp}>"

//    s"$pred(${args.map(_.pp).mkString(", ")})${ppCard(card)}${tag.pp}"
    s"$pred_with_info(${args.map(_.pp).mkString(", ")})${ppCard(card)}"
  }


  override def compare(that: Heaplet): Int = that match {
    case SApp(pred1, args1, tag, card) =>
      val c1 = this.pred_with_info.compareTo(pred1)
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
    case SApp(p, as, _, c) if pred_with_info == p => Some((card :: args.toList).zip(c :: as.toList).toMap)
    case _ => None
  }

  override def unifySyntactic(that: Heaplet, unificationVars: Set[Var]): Option[Subst] = that match {
    case SApp(p, Seq(), _, c) if pred_with_info == p => card.unifySyntactic(c, unificationVars)
    case app@SApp(p, a +: as, _, _) if pred_with_info == p => for {
      sub1 <- args.head.unifySyntactic(a, unificationVars)
      sub2 <- this.copy(args = args.tail).subst(sub1).unifySyntactic(app.copy(args = as), unificationVars)
    } yield sub1 ++ sub2
    case _ => None
  }

}

case class Ref(lft: Lifetime, mut: Boolean) extends PrettyPrinting {
  override def pp: String = if (mut) { s"${lft.pp} mut " } else { s"${lft.pp} " }
  def subst(sigma: Map[Var, Expr]): Ref = {
    this.copy(lft = lft.subst(sigma))
  }
  def sig: String = if (mut) { s"&${lft.rustLft.get} mut " } else { s"&${lft.rustLft.get} " }
}

/**
  *       Rust predicate application. For example:
  *       x: &a mut i32(value)<&blocked_by>
  */
case class RApp(priv: Boolean, field: Var, ref: Option[Ref], pred: Ident, fnSpec: Seq[Expr], blocked: Lifetime, tag: PTag) extends Heaplet {
  def toSApp: SApp = SApp(pred, fnSpec, tag, IntConst(0))

  def isBorrow: Boolean = ref.isDefined
  def isBlocked: Boolean = blocked.getNamed.isDefined

  // If the entire fnSpec is existential, then no point writing
  // def isWriteableBorrow(existentials: Set[Var]): Boolean = isBorrow && ref.get.mut && fnSpec.forall(_.vars.subsetOf(existentials))

  // Can be copied out immediately
  def isPrim(predicates: PredicateEnv): Boolean = predicates(pred).isPrim

  // Should be folded/unfolded after non-cyclic things
  def isCyclic(predicates: PredicateCycles): Boolean = predicates(pred)

  override def resolveOverloading(gamma: Gamma): Heaplet = this.copy(fnSpec = fnSpec.map(_.resolveOverloading(gamma)))

  override def pp: String = {
    val privS = if (priv) "priv " else ""
    val refS = ref.map(_.pp).getOrElse("")
    s"$privS${field.pp} : $refS$pred(${fnSpec.map(_.pp).mkString(", ")})${blocked.getNamed.fold("")("<"+ _.pp +">")}${tag.pp}"
  }


  override def compare(that: Heaplet): Int = that match {
    case RApp(_, field1, _, pred1, _, _, _) =>
      if (pred.compareTo(pred1) != 0) return pred.compareTo(pred1)
      assert(field.compareTo(field1) != 0)
      return field.compareTo(field1)
    case _ => super.compare(that)
  }

  def subst(sigma: Map[Var, Expr]): Heaplet = {
    this.copy(
      field = field.subst(sigma).asInstanceOf[Var],
      ref = ref.map(_.subst(sigma)),
      fnSpec = fnSpec.map(_.subst(sigma)),
      blocked = blocked.subst(sigma)
    )
  }

  def resolve(gamma: Gamma, env: Environment): Option[Gamma] = {
    if (!(env.predicates contains pred)) {
      throw SynthesisException(s"predicate $pred is undefined")
    }

    val newGamma =
      if (ref.isDefined && ref.get.lft.getNamed.isDefined) gamma + (field -> LocType) + (ref.get.lft.getNamed.get.name -> IntType) 
      else gamma + (field -> LocType)
    val formals = env.predicates(pred).params
    assert(formals.length == fnSpec.length)
    if (formals.length == fnSpec.length) {
      (formals, fnSpec).zipped.foldLeft[Option[Gamma]](Some(newGamma)) { case (go, (formal, actual)) => go match {
        case None => None
        case Some(g) => actual.resolve(g, Some(formal._2))
      }
      }
    } else None
  }

  override def getTag: Option[PTag] = Some(tag)

  override def setTag(t: PTag): Heaplet = this.copy(tag = t)

  def setRef(newRef: Ref): RApp = {
    assert(ref.isEmpty)
    this.copy(ref = Some(newRef))
  }

  override def unify(that: Heaplet): Option[ExprSubst] = that match {
    case RApp(pri, tgt, Some(r), p, spec, lft, _) if field == tgt => {
      assert(pri == priv && p == pred && r == ref.get)
      Some((blocked :: fnSpec.toList).zip(lft :: spec.toList).toMap)
    }
    // Neither can be private. Also if exactly one lifetime is Nil,
    // then relies on substitution kicking in before anything else for soundness!
    case RApp(false, tgt, r, p, spec, lft, _) if pred == p && r.map(_.mut) == ref.map(_.mut) && !priv =>
      val subs = (field :: blocked :: fnSpec.toList).zip(tgt :: lft :: spec.toList).toMap
      val subsLft = if (r.isDefined) subs + (ref.get.lft.getNamed.get -> r.get.lft.getNamed.get) else subs
      Some(subsLft)
      // TODO: should only unify borrows (field -> tgt) if in a call goal!
    case _ => None
  }

  override def unifySyntactic(that: Heaplet, unificationVars: Set[Var]): Option[Subst] = None
}

case class SFormula(chunks: List[Heaplet]) extends PrettyPrinting with HasExpressions[SFormula] {
  def resolveOverloading(gamma: Gamma): SFormula = {
    this.copy(chunks = chunks.map(_.resolveOverloading(gamma)))
  }

  override def pp: Ident = if (chunks.isEmpty) "emp" else {
    def pt(l: List[Heaplet]) = l.map(_.pp).sortBy(x => x)

    List(ptss, apps, blocks, rapps).flatMap(pt).mkString(" ** ")
  }

  def blocks: List[Block] = for (b@Block(_, _) <- chunks) yield b

  def apps: List[SApp] = for (b@SApp(_, _, _, _) <- chunks) yield b

  def ptss: List[PointsTo] = for (b@PointsTo(_, _, _) <- chunks) yield b

  def rapps: List[RApp] = for (b@RApp(_, _, _, _, _, _, _) <- chunks) yield b

  // RApps for the function signature
  def sigRapps: List[RApp] = for (b@RApp(false, _, _, _, _, _, _) <- chunks) yield b

  def borrows: List[RApp] = rapps.filter(_.isBorrow)
  def owneds: List[RApp] = rapps.filter(!_.isBorrow)
  def prims(predicates: PredicateEnv): List[RApp] = rapps.filter(_.isPrim(predicates))

  def subst(sigma: Map[Var, Expr]): SFormula = SFormula(chunks.map(_.subst(sigma)))

  // Collect certain sub-expressions
  def collect[R <: Expr](p: Expr => Boolean): Set[R] = {
    chunks.foldLeft(Set.empty[R])((a, h) => a ++ h.collect(p))
  }

  def setTagAndRef(r: RApp): SFormula = SFormula(chunks.map(_.setTag(r.tag.incrUnrolls) match {
    case h@RApp(_, _, _, _, _, _, _) if r.isBorrow => h.setRef(r.ref.get)
    case h => h
  }))
  def setSAppTags(t: PTag): SFormula = SFormula(chunks.map(h => h.setTag(t)))

  def callTags: List[Int] = chunks.flatMap(_.getTag).map(_.calls)

  def isEmp: Boolean = chunks.isEmpty

  def block_size (expr: Expr) = blocks find { case Block(loc,_) if loc == expr => true case _ => false } map (v => v.sz)

  // Add h to chunks (multiset semantics)
  def **(h: Heaplet): SFormula = SFormula(h :: chunks)

  // Add all chunks from other (multiset semantics)
  def **(other: SFormula): SFormula = SFormula(chunks ++ other.chunks)

  // Remove h from this formula (multiset semantics)
  def -(h: Heaplet): SFormula = SFormula(chunks.diff(List(h)))

  // Remove all chunks present in other (multiset semantics)
  def -(other: SFormula): SFormula = SFormula(chunks.diff(other.chunks))

  // Add chunks from other (set semantics)
  def +(other: SFormula): SFormula = SFormula((chunks ++ other.chunks).distinct)

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
    val rappOwnedsProfile = owneds.groupBy(r => r.pred).mapValues(_.length)
    val rappBorrowsProfile = borrows.groupBy(r => r.pred).mapValues(_.length)
    val appProfile = apps.groupBy(_.pred_with_info).mapValues(_.length)
    val blockProfile = blocks.groupBy(_.sz).mapValues(_.length)
    val ptsProfile = ptss.groupBy(_.offset).mapValues(_.length)
    SProfile((rappOwnedsProfile, rappBorrowsProfile), appProfile, blockProfile, ptsProfile)
  }


  // Size of the formula (in AST nodes)
  def size: Int = chunks.map(_.size).sum

  def cost: Int = chunks.map(_.cost).sum

  //  def cost: Int = chunks.foldLeft(0)((m, c) => m.max(c.cost))
}

/**
  * Profile of a spatial formula (contains properties that cannot be changed by unification)
  * @param apps how maybe applications there are of each predicate?
  * @param blocks how many blocks there are of each size?
  * @param ptss how many points-to chunks there are with each offset?
  */
case class SProfile(rapps: (Map[Ident, Int], Map[Ident, Int]), apps: Map[Ident, Int], blocks: Map[Int, Int], ptss: Map[Int, Int])



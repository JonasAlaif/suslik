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
        field.collect(p) ++ ref.flatMap(_.lft.collect(p)) ++
          fnSpec.foldLeft(acc)((a, e) => a ++ e.collect(p)) ++ lft.foldLeft(acc)((a, e) => a ++ e.collect(p))
    }

    collector(Set.empty)(this)
  }

  // Unify with that modulo theories:
  // produce pairs of expressions that must be equal for the this and that to be the same heaplet
  def unify(that: Heaplet, isReborrow: Boolean, gamma: Gamma): Option[ExprSubst]

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
    case SApp(_, _, PTag(c, u), _) => 2 + (4*c + u)
    case RApp(_, _, _, _, _, _, PTag(c, u)) => 2 + (4*c + u)
    case _ => 1
  }

  def postCost: Int = this match {
    case SApp(_, _, PTag(c, u), _) => 2 + 4*(c + u)
    case r@RApp(_, _, _, _, _, _, PTag(c, u)) if !r.isBorrow => 2 + 4*(c + u)
    case RApp(_, _, _, _, _, _, _) => 0
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
  override def unify(that: Heaplet, isReborrow: Boolean, gamma: Gamma): Option[ExprSubst] = that match {
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

  override def unify(that: Heaplet, isReborrow: Boolean, gamma: Gamma): Option[ExprSubst] = that match {
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

  override def unify(that: Heaplet, isReborrow: Boolean, gamma: Gamma): Option[ExprSubst] = that match {
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

case class Ref(lft: Named, mut: Boolean, beenAddedToPost: Boolean) extends PrettyPrinting {
  override def pp: String = if (mut) { s"${lft.pp} mut " } else { s"${lft.pp} " }
  def subst(sigma: Map[Var, Expr]): Option[Ref] = {
    for {
      lft <- lft.subst(sigma).getNamed
    } yield this.copy(lft = lft)    
  }
  def sig: String = if (mut) { s"&${lft.rustLft.get} mut " } else { s"&${lft.rustLft.get} " }
}

/**
  *       Rust predicate application. For example:
  *       x: &a mut i32(value)<&blocked_by>
  */
case class RApp(priv: Boolean, field: Var, ref: List[Ref], pred: Ident, fnSpec: Seq[Expr], blocked: Set[Named], tag: PTag) extends Heaplet {
  def toSApp: SApp = SApp(pred, fnSpec, tag, IntConst(0))

  val isBorrow: Boolean = ref.length > 0
  def popRef: RApp = this.copy(field = Var("de_" + field.name),
    ref = (if (ref.tail.head.mut) ref.head else ref.tail.head.copy(beenAddedToPost = ref.head.beenAddedToPost))
      :: ref.tail.tail
  )
  val hasBlocker: Boolean = blocked.nonEmpty

  def isWriteableRef(existentials: Set[Var]): Boolean = !priv && isBorrow && ref.head.mut && ref.head.beenAddedToPost

  // If the entire fnSpec is existential, then no point writing
  // def isWriteableBorrow(existentials: Set[Var]): Boolean = isBorrow && ref.get.mut && fnSpec.forall(_.vars.subsetOf(existentials))

  // Can be copied out immediately
  def isPrim(predicates: PredicateEnv): Boolean = predicates(pred).isPrim

  // Should be folded/unfolded after non-cyclic things
  def isCyclic(predicates: PredicateCycles): Boolean = predicates(pred)

  def isOpaque(predicates: PredicateEnv): Boolean = predicates(pred).isOpaque

  def block: RApp = {
    assert(!hasBlocker)
    this.copy(blocked = Set(Named(Var(field.name + "-L"))))
  }

  def fnSpecNoLftTyped(gamma: Gamma): Seq[((Expr, SSLType), Int)] =
    this.fnSpec.map(arg => (arg, arg.getType(gamma).get)).filter(_._2 != LifetimeType).zipWithIndex
  def refreshFnSpec(gamma: Gamma, vars: Set[Var]): RApp = {
      val newVars = this.fnSpec.map(e => (e, e.getType(gamma).get)).zipWithIndex.map(
        i => if (i._1._2 != LifetimeType) (Var(this.field.pp + i._2), i._1._2) else i._1
      )
      val sub = refreshVars(newVars.flatMap(i => if (i._2 != LifetimeType) Some(i._1.asInstanceOf[Var]) else None).toList, vars)
      this.copy(fnSpec = newVars.map(i => if (i._2 != LifetimeType) sub(i._1.asInstanceOf[Var]) else i._1))
  }
  def mkOnExpiry(gamma: Gamma, isPost: Option[Boolean]): PFormula =
    PFormula(this.fnSpecNoLftTyped(gamma).map(arg => arg._1._1 |===| OnExpiry(isPost, List.fill(this.ref.length)(false), this.field, arg._2, arg._1._2)).toSet
    ).resolveOverloading(gamma)

  override def resolveOverloading(gamma: Gamma): Heaplet = this.copy(fnSpec = fnSpec.map(_.resolveOverloading(gamma)))

  override def pp: String = {
    val privS = if (priv) "priv " else ""
    val refS = ref.map(_.pp).mkString("")
    val ppBlocked = if (hasBlocker) blocked.map(_.pp).mkString("< ", " + ", " >") else ""
    s"$privS${field.pp} : $refS$pred(${fnSpec.map(_.pp).mkString(", ")})$ppBlocked${tag.pp}"
  }


  override def compare(that: Heaplet): Int = that match {
    case RApp(_, field1, _, pred1, _, _, _) =>
      if (pred.compareTo(pred1) != 0) return pred.compareTo(pred1)
      assert(field.compareTo(field1) != 0)
      return field.compareTo(field1)
    case _ => super.compare(that)
  }

  def subst(sigma: Map[Var, Expr]): Heaplet =
    throw new SynthesisException(s"Trying to subst `$pp`")
  def substKill(sigma: Map[Var, Expr]): Option[Heaplet] = {
    val r = ref.flatMap(_.subst(sigma))
    // My lft was killed
    if (isBorrow && r.isEmpty) None
    else Some(this.copy(
      field = field.subst(sigma).asInstanceOf[Var],
      ref = r,
      fnSpec = fnSpec.map(_.subst(sigma)),
      blocked = blocked.flatMap(_.subst(sigma).getNamed)
    ))
  }

  def resolve(gamma: Gamma, env: Environment): Option[Gamma] = {
    if (!(env.predicates contains pred)) {
      throw SynthesisException(s"predicate $pred is undefined")
    }

    val newGamma = gamma ++ ref.map(_.lft.getNamed.get.name -> LifetimeType).toMap + (field -> LocType)
    val formals = env.predicates(pred).params
    assert(formals.length == fnSpec.length)
    if (formals.length == fnSpec.length) {
      (formals, fnSpec).zipped.foldLeft[Option[Gamma]](Some(newGamma)) { case (go, (formal, actual)) => go match {
        case None => None
        case Some(g) => actual.resolve(g, Some(formal._2)) match {
          case None => throw SepLogicException(s"Resolution error: ${actual.pp}: ${formal._2} vs ${g(actual.asInstanceOf[Var])}")
          case Some(g1) => Some(g1)
        }
      }
      }
    } else None
  }

  override def getTag: Option[PTag] = Some(tag)

  override def setTag(t: PTag): Heaplet = this.copy(tag = t)

  def setRef(newRef: Ref): RApp = this.copy(ref = newRef :: this.ref)

  // this is the RApp in pre (source), that is in post (target)
  override def unify(that: Heaplet, isReborrow: Boolean, gamma: Gamma): Option[ExprSubst] = that match {
    // Unifying borrow in pre/post which has been duplicated with beenAddedToPost
    case o@RApp(pri, tgt, rs, p, spec, _, _) if !isReborrow && this.field == tgt && o.isBorrow && (!this.hasBlocker || o.hasBlocker) => {
      assert(pri == this.priv && p == this.pred && this.ref == rs && this.ref.head.beenAddedToPost)
      val subst = this.fnSpec.zip(spec.toList)
      // Not necessary (since if o.hasBlocker then it's o.fnSpec is existential and we just bound that to this.fnSpec)
      // if (o.hasBlocker) subst ++ o.fnSpecNoLftTyped(gamma).map(arg => arg._1._1 -> OnExpiry(Some(true), true :: List.fill(this.ref.length-1)(false), this.field, arg._2, arg._1._2))
      Some(subst.toMap)
    }
    // Reborrowing
    case o@RApp(false, tgt, r, p, spec, _, _)
      if this.pred == p && this.isBorrow && o.isBorrow &&
        // Either tgt is immut or src is mut
        isReborrow && (this.ref.head.mut || !r.head.mut) && r.tail == this.ref.tail &&
        !this.priv =>
      // Doing reborrow (src `this.hasBlocker` may or may not be true, depending on if it's in pre or post):
      assert(!o.hasBlocker)
      val subs = (this.field :: this.fnSpec.toList).zip(tgt :: spec.toList).toMap
      Some(subs)
      // TODO: should only unify borrows (field -> tgt) if in a call goal!
    // Unifying owned
    // Neither can be private.
    case o@RApp(false, tgt, r, p, spec, _, _)
      if !isReborrow && this.pred == p && !o.isBorrow && !this.isBorrow && !this.hasBlocker && !this.priv =>
      // Non-borrow unify
      val subs = (this.field :: this.fnSpec.toList).zip(tgt :: spec.toList).toMap
      Some(subs)
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
  def enableAddBrrwsToPost: SFormula = SFormula(chunks.map {
    case b@RApp(_, _, r, _, _, _, _) if r.length > 0 && r.head.beenAddedToPost => b.copy(ref = r.head.copy(beenAddedToPost = false) :: r.tail)
    case h => h
  })
  def toCallGoal(post: Boolean): SFormula = SFormula(chunks.filter {
    case RApp(true, _, _, _, _, _, _) => false
    case r@RApp(_, _, ref, _, _, _, _) if post && r.isBorrow && ref.head.beenAddedToPost => false
    case _ => true
  })
  def toFuts(gamma: Gamma): PFormula = PFormula(chunks.flatMap {
    case r@RApp(_, field, ref, _, fnSpec, _, _) if r.isBorrow && ref.head.beenAddedToPost =>
      fnSpec.map(arg => (arg, arg.getType(gamma).get)).filter(_._2 != LifetimeType)
      .zipWithIndex.map(arg => arg._1._1 |===| OnExpiry(None, true :: List.fill(ref.length-1)(false), field, arg._2, arg._1._2))
    case _ => Seq.empty
  }.toSet).resolveOverloading(gamma)

  def blockRapps(r: RApp): SFormula = if (!r.hasBlocker) this else SFormula(chunks.map {
    case b@RApp(_, _, _, _, _, _, _) => b.copy(blocked = r.blocked)
    case h => h
  })

  def subst(sigma: Map[Var, Expr]): SFormula = SFormula(chunks.flatMap {
    case b@RApp(_, _, _, _, _, _, _) => b.substKill(sigma)
    case h => Some(h.subst(sigma))
  })

  // Collect certain sub-expressions
  def collect[R <: Expr](p: Expr => Boolean): Set[R] = {
    chunks.foldLeft(Set.empty[R])((a, h) => a ++ h.collect(p))
  }

  def setTagAndRef(r: RApp): SFormula = {
    assert(r.ref.length <= 1)
    SFormula(chunks.map(_.setTag(r.tag.incrUnrolls) match {
      case h@RApp(_, _, _, _, _, _, _) if r.isBorrow => h.setRef(r.ref.head)
      case h => h
    }))
  }
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
      case Some(g) => h.resolve(g, env) match {
        case None => throw SepLogicException(s"Resolution error in conjunct: ${h.pp}")
        case Some(g1) => Some(g1)
      }
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
  def postCost: Int = chunks.map(_.postCost).sum

  //  def cost: Int = chunks.foldLeft(0)((m, c) => m.max(c.cost))
}

/**
  * Profile of a spatial formula (contains properties that cannot be changed by unification)
  * @param apps how maybe applications there are of each predicate?
  * @param blocks how many blocks there are of each size?
  * @param ptss how many points-to chunks there are with each offset?
  */
case class SProfile(rapps: (Map[Ident, Int], Map[Ident, Int]), apps: Map[Ident, Int], blocks: Map[Int, Int], ptss: Map[Int, Int])



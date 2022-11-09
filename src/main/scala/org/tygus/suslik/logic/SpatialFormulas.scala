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
  def unify(that: Heaplet): Option[ExprSubst]

  // Unify syntactically: find a subst for existentials in this
  // that makes it syntactically equal to that
  def unifySyntactic(that: Heaplet, unificationVars: Set[Var]): Option[Subst]

  def compare(that: Heaplet): Int = this.pp.compare(that.pp)

  def resolve(gamma: Gamma, env: Environment): Option[Gamma]

  def getTag: Option[PTag] = None

  def setTag(t: PTag): Heaplet = this
  def getPred: Ident = ???

  def eqModTags(other: Heaplet): Boolean = {
    this.setTag(PTag()) == other.setTag(PTag())
  }

  // If this is a predicate instance, assume that from is too and copy its tag
  def copyTag(tag: PTag): Heaplet = this match {
    case SApp(pred, args, _, card) => SApp(pred, args, tag, card)
    case r@RApp(_, _, _, _, _, _, _) => r.copy(tag = tag)
    case _ => this
  }

  // Size of the heaplet (in AST nodes)
  def size: Int = this match {
    case PointsTo(loc, _, value) => 1 + loc.size + value.size
    case Block(loc, _) => 1 + loc.size
    case SApp(_, args, _, _) => args.map(_.size).sum
    case RApp(_, _, _, _, fnSpec, _, _) => 1 + fnSpec.map(_.size).sum
  }

  def cost(predicates: PredicateEnv, cycles: PredicateCycles): Int = this match {
    case SApp(_, _, t@PTag(c, u, _, ec), _) => 0 + 2*c*c+ 3*t.recursions + u + ec
    case r:RApp if !r.isBorrow && !cycles(r.pred) && r.isCopy(predicates) && !r.priv => 1
    case r@RApp(priv, _, _, _, _, _, t@PTag(c, u, _, ec)) =>// if (priv && r.isBorrow) 0 else 
      0 + 2*c*c + 3*t.recursions + u + ec
    case _ => 1
  }

  def postCost(preBrrws: List[RApp]): Int = this match {
    case SApp(_, _, t@PTag(c, u, _, ec), _) => 0 + 4*(c + u + t.recursions) + ec
    case r:RApp if r.isBorrow && r.ref.head.beenAddedToPost => {
      // Punish not expiring early
      preBrrws.filter(_.field.name.endsWith(r.field.name)).map(_.tag.unrolls - r.tag.unrolls)
      // TODO: There may be no fields in a ref that was unfolded in the pre, handle this inelegantly by defaulting to 20
        .reduceOption(_ max _).getOrElse(20) + r.tag.extraCost
    }
    case r@RApp(priv, _, _, _, _, _, t@PTag(c, u, _, ec)) => {
      assert(c == 0)
      if (priv) 0 else 0 + 3*t.recursions + u + ec
    }
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

case class PTag(calls: Int = 0, unrolls: Int = 0, pastTypes: (List[Ident], Int) = (List.empty, 0), extraCost: Int = 0) extends PrettyPrinting {
  override def pp: String = this match {
    case PTag(0, 0, _, 0) => "" // Default tag
    case _ => s"[$calls,$unrolls,$recursions,$extraCost]"
  }
  def incrUnrolls(ty: Ident, isCyc: Boolean): PTag = {
    val preCyc = this.pastTypes._1.dropWhile(_ != ty)
    if (preCyc.length == 0) {
      val pastTypes = (if (ty == "") this.pastTypes._1 else ty :: this.pastTypes._1, if (isCyc) this.pastTypes._2 else 0)
      this.copy(unrolls = this.unrolls+1, pastTypes = pastTypes)
    }
    else this.copy(unrolls = this.unrolls+1, pastTypes = (preCyc, if (isCyc) this.pastTypes._2+1 else 0))
  }
  def incrCalls: PTag = this.copy(calls = calls+1)
  val recursions: Int = pastTypes._2
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
  override def getPred: Ident = this.pred

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

case class Ref(lft: NamedLifetime, mut: Boolean, beenAddedToPost: Boolean) extends PrettyPrinting {
  override def pp: String = s"${lft.pp} " + (if (mut) "mut " else "")
  def subst(sigma: Map[Var, Expr]): Option[Ref] = {
    for {
      lft <- lft.subst(sigma).getNamed
    } yield this.copy(lft = lft)    
  }
  def sig: String = s"&${lft.sig}" + (if (mut) "mut " else "")
}

/**
  *       Rust predicate application. For example:
  *       x: &a mut i32(value)<&blocked_by>
  */
case class RApp(priv: Boolean, field: Var, ref: List[Ref], pred: Ident, fnSpec: Seq[Expr], blocked: Option[Lifetime], tag: PTag) extends Heaplet {
  def toSApp: SApp = SApp(pred, fnSpec, tag, IntConst(0))

  val isBorrow: Boolean = ref.length > 0
  def fnSpecLfts: Seq[Lifetime] = this.fnSpec.flatMap(f => {
    val lfts = f.collect[Lifetime](_.isInstanceOf[Lifetime])
    assert(lfts.size == 0 || (lfts.size == 1 && lfts.head == f))
    lfts.headOption
  })
  def potentialTgtLfts: List[NamedLifetime] = this.ref.flatMap(ref => if (ref.beenAddedToPost) None else Some(ref.lft)) ++ this.fnSpecLfts.flatMap(_.getNamed)
  def popRef: RApp = this.copy(field = Var("de_" + field.name),
    ref = (if (ref.tail.head.mut) ref.head else ref.tail.head.copy(beenAddedToPost = ref.head.beenAddedToPost))
      :: ref.tail.tail,
    tag = this.tag.incrUnrolls("", true)
  )
  def getBlocker: Option[NamedLifetime] = blocked.flatMap(_.getNamed)
  val hasBlocker: Boolean = blocked.isDefined && blocked.get.getNamed.isDefined
  val canBeBlocked: Boolean = isBorrow && getBlocker.isEmpty && ref.head.beenAddedToPost
  val isUnblockable: Boolean = !canBeBlocked

  def isWriteableRef(existentials: Set[Var]): Boolean = !priv && isBorrow && ref.head.mut && ref.head.beenAddedToPost

  // If the entire fnSpec is existential, then no point writing
  // def isWriteableBorrow(existentials: Set[Var]): Boolean = isBorrow && ref.get.mut && fnSpec.forall(_.vars.subsetOf(existentials))

  // Can be copied out immediately
  def isPrim(predicates: PredicateEnv): Boolean = predicates(pred).isPrim
  def isCopy(predicates: PredicateEnv): Boolean = predicates(pred).isCopy
  def isDrop(predicates: PredicateEnv): Boolean = predicates(pred).isDrop

  // Should be folded/unfolded after non-cyclic things
  def isCyclic(predicates: PredicateCycles): Boolean = predicates(pred)

  def isOpaque(predicates: PredicateEnv): Boolean = predicates(pred).isOpaque

  def mkUnblockable: RApp = {
    assert(!hasBlocker)
    if (this.isBorrow && this.ref.head.mut) this.copy(blocked = Some(NilLifetime)) else this
  }
  def block(lft: NamedLifetime): RApp = {
    assert(!hasBlocker)
    this.copy(blocked = Some(lft))
  }

  def fnSpecNoLftTyped(gamma: Gamma): Seq[((Expr, SSLType), Int)] =
    this.fnSpec.map(arg => (arg, arg.getType(gamma).get)).zipWithIndex.filter(_._1._2 != LifetimeType)
  def refreshFnSpec(gamma: Gamma, vars: Set[Var], wrapInAlwaysExists: Boolean = false): RApp = {
      val newVars = this.fnSpec.map(e => (e, e.getType(gamma).get)).zipWithIndex.map(
        i => if (i._1._2 != LifetimeType) (Var(this.field.pp + i._2), i._1._2) else i._1
      )
      val sub = refreshVars(newVars.flatMap(i => if (i._2 != LifetimeType) Some(i._1.asInstanceOf[Var]) else None).toList, vars)
      this.copy(fnSpec = newVars.map(i => if (i._2 != LifetimeType) {
          val v = sub(i._1.asInstanceOf[Var])
          if (wrapInAlwaysExists) AlwaysExistsVar(v) else v
        } else i._1
      ))
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
  // Can kill lft
  def substKill(sigma: Map[Var, Expr]): Option[Heaplet] = {
    val r = ref.map(_.subst(sigma))
    // My lft was killed
    if (r.exists(_.isEmpty)) None
    else Some(this.copy(
      field = field.subst(sigma).asInstanceOf[Var],
      ref = r.map(_.get),
      fnSpec = fnSpec.map(_.subst(sigma)),
      blocked = if (this.blocked.isEmpty || this.blocked.get == NilLifetime) blocked
                else blocked.flatMap(_.subst(sigma).getNamed)
    ))
  }

  def resolve(gamma: Gamma, env: Environment): Option[Gamma] = {
    if (!(env.predicates contains pred)) {
      throw SynthesisException(s"predicate $pred is undefined")
    }

    val refGamma = ref.flatMap(_.lft.getName).map(_ -> LifetimeType).toMap
    val newGamma = gamma ++ refGamma + (field -> LocType)
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
  override def getPred: Ident = this.pred

  def setRef(newRef: Ref): RApp = this.copy(ref = newRef :: this.ref)

  // this is the RApp in pre (source), that is in post (target)
  override def unify(that: Heaplet): Option[ExprSubst] = that match {
    // Unifying borrow in pre/post which has been duplicated with beenAddedToPost
    case o@RApp(pri, tgt, rs, p, spec, _, _) if this.field == tgt && o.isBorrow && (!this.hasBlocker || o.canBeBlocked) => {
      assert(pri == this.priv && p == this.pred && this.ref == rs && this.ref.head.beenAddedToPost, "this: " + this + " vs that: " + that)
      val subst = this.fnSpec.zip(spec.toList)
      Some(subst.toMap)
    }
    case o@RApp(false, tgt, r, p, spec, _, _)
      if this.pred == p && !o.isBorrow && !this.isBorrow && !this.hasBlocker && !this.priv =>
      // Non-borrow unify
      val subs = (this.field :: this.fnSpec.toList).zip(tgt :: spec.toList).toMap
      Some(subs)
    case _ => None
  }

  // this is the RApp in pre (source), that is in post (target)
  def reborrow(that: RApp, outlivesRels: Set[(NamedLifetime, NamedLifetime)]): Option[ExprSubst] = {
    assert(that.ref.head.beenAddedToPost || that.blocked.isEmpty, "That: " + that + "\nwith " + this)
    if (
      this.canBeBlocked && !this.priv &&
      !that.ref.head.beenAddedToPost && !that.priv &&
      this.pred == that.pred &&
      // Mutability matches
      (this.ref.head.mut || !that.ref.head.mut) &&
      // Have to be equal (could potentially have the situation `'a: 'b, 'b: 'a` but then we should ensure that one is subst fo the other)
      this.ref.tail.map(_.mut) == that.ref.tail.map(_.mut) &&
        // this.fnSpecLfts == that.fnSpecLfts &&
      // Lifetimes existenatials or
      (this.ref.head.lft.isExistential || that.ref.head.lft.isExistential || this.ref.head.lft == StaticLifetime ||
      // Lifetimes outlive
        this.ref.head.lft == that.ref.head.lft || outlivesRels.contains((that.ref.head.lft, this.ref.head.lft)))
    ) {
      val sub = (this.field :: this.fnSpec.toList ++ this.ref.tail.map(_.lft))
            .zip(that.field :: that.fnSpec.toList ++ that.ref.zipWithIndex.tail.map(r => {
              if (r._1.lft.isExistential && !this.ref.head.mut) this.ref(r._2).lft else r._1.lft
            })).toMap
      Some(sub)
    } else None
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
  def toFormals: RustFormals = this.sigRapps.map(r => (r.field, r.ref, r.pred))

  def potentialTgtLfts: Set[NamedLifetime] = rapps.flatMap(_.potentialTgtLfts).toSet
  def borrows: List[RApp] = rapps.filter(_.isBorrow)
  def owneds: List[RApp] = rapps.filter(!_.isBorrow)
  def prims(predicates: PredicateEnv): List[RApp] = rapps.filter(_.isPrim(predicates))
  def copies(predicates: PredicateEnv): List[RApp] = borrows.filter(_.isCopy(predicates))
  def enableAddBrrwsToPost: SFormula = SFormula(chunks.map {
    case b:RApp if b.ref.length > 0 && b.ref.head.beenAddedToPost => b.copy(ref = b.ref.head.copy(beenAddedToPost = false) :: b.ref.tail)
    case h => h
  })
  def unblockLft(l: Named): SFormula = SFormula(chunks.map {
    case r:RApp if r.blocked.isDefined && r.blocked.get.getNamed.get == l => r.copy(blocked = None)
    case h => h
  })
  def wrapInAE: SFormula = SFormula(chunks.map {
    case r:RApp => r.copy(fnSpec = r.fnSpec.map {
      case v: Var => AlwaysExistsVar(v)
      case x => x
    })
    case h => h
  })
  def toCallGoal(post: Boolean): SFormula = SFormula(chunks.flatMap {
    case RApp(true, _, _, _, _, _, _) => None
    case r:RApp if r.isBorrow && r.ref.head.beenAddedToPost => if (post) None else {
      assert(r.blocked.flatMap(_.getNamed).isEmpty)
      Some(r.copy(ref = r.ref.head.copy(beenAddedToPost = false) :: r.ref.tail, tag = PTag(), blocked = r.blocked.flatMap(_.getNamed)))
    }
    case h => Some(h.setTag(PTag()))
  })
  def toFuts(gamma: Gamma): PFormula = PFormula(chunks.flatMap {
    case r@RApp(_, field, ref, _, fnSpec, _, _) if r.isBorrow && ref.head.mut && ref.head.beenAddedToPost =>
      r.fnSpecNoLftTyped(gamma)
        .map(arg => arg._1._1 |===| OnExpiry(None, true :: List.fill(ref.length-1)(false), field, arg._2, arg._1._2))
    case _ => Seq.empty
  }.toSet).resolveOverloading(gamma)

  def mkUnblockable: SFormula = SFormula(chunks.map {
    case b:RApp => b.mkUnblockable
    case h => h
  })

  def subst(sigma: Map[Var, Expr]): SFormula = SFormula(chunks.flatMap {
    case b:RApp => b.substKill(sigma)
    case h => Some(h.subst(sigma))
  })

  // Collect certain sub-expressions
  def collect[R <: Expr](p: Expr => Boolean): Set[R] = {
    chunks.foldLeft(Set.empty[R])((a, h) => a ++ h.collect(p))
  }

  def setTagAndRef(r: RApp, cycPreds: PredicateCycles): SFormula = {
    assert(r.ref.length <= 1)
    SFormula(chunks.map(c => c.setTag(r.tag.incrUnrolls(r.pred, cycPreds(c.getPred))) match {
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

  def cost(predicates: PredicateEnv, cycles: PredicateCycles): Int = chunks.map(_.cost(predicates, cycles)).sum
  def postCost(preBrrws: List[RApp]): Int = chunks.map(_.postCost(preBrrws)).sum

  //  def cost: Int = chunks.foldLeft(0)((m, c) => m.max(c.cost))
}

/**
  * Profile of a spatial formula (contains properties that cannot be changed by unification)
  * @param apps how maybe applications there are of each predicate?
  * @param blocks how many blocks there are of each size?
  * @param ptss how many points-to chunks there are with each offset?
  */
case class SProfile(rapps: (Map[Ident, Int], Map[Ident, Int]), apps: Map[Ident, Int], blocks: Map[Int, Int], ptss: Map[Int, Int])



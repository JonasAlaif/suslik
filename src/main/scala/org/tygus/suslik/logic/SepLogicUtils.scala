package org.tygus.suslik.logic

import org.tygus.suslik.SSLException
import org.tygus.suslik.language.Expressions._
import org.tygus.suslik.logic.smt.SMTSolving
import org.tygus.suslik.synthesis.SynthesisException

/**
  * Utilities for spatial formulae
  *
  * @author Nadia Polikarpova, Ilya Sergey
  */

trait SepLogicUtils extends PureLogicUtils {

  /**
    * A name used to refer to the size cardinality of the enclosing inductive predicate
    * from within its definition
    */
  val selfCardVar = Var("self_card")

  protected def slAssert(assertion: Boolean, msg: String): Unit = if (!assertion) throw SepLogicException(msg)

  def cardName(n: String) = s"${n}_card"

  def emp: SFormula = SFormula(Nil, TypeMap())

  def singletonHeap(h: Heaplet): SFormula = mkSFormula(List(h))

  def mkSFormula(hs: List[Heaplet]) = {
    var tps = TypeMap((for (b@SApp(_, _, _, _) <- hs) yield b.args(0).asInstanceOf[Var].name -> (List(), b.pred)).toMap)
    var ptss_list = for (b@PointsTo(_, _, _, _) <- hs) yield b
    var old_len = ptss_list.length + 1
    while (ptss_list.length != old_len) {
      old_len = ptss_list.length
      ptss_list = ptss_list.filter(pts =>
        if (pts.offset != 0) false else tps.get(pts.value) match {
          case Some((refs, t)) => {
            //tps = tps + (pts.loc.asInstanceOf[Var].name -> (pts.perm :: refs, t))
            false
          }
          case None => true
        }
      )
    }
    for (PointsTo(_, _, Var(name), _) <- ptss_list) {
      tps = tps + (name -> (List(), "int"))
    }
    //println("CREATED: " + hs + " with types " + tps)
    SFormula(hs, tps)
  }

  /**
    * Get the heaplet satisfying the predicate
    */
  def findHeaplet(p: (Heaplet) => Boolean,
                  sigma: SFormula): Option[Heaplet] = sigma.chunks.find(p)

  /**
    * Get heaplets from pre and post satisfying a relation
    */
  def findMatchingHeaplets(pl: Heaplet => Boolean,
                           pr: (Heaplet, Heaplet) => Boolean,
                           pre: SFormula,
                           post: SFormula): Option[(Heaplet, Heaplet)] = {
    (for {hl <- pre.chunks if pl(hl)
          hr <- post.chunks if pr(hl, hr)} yield (hl, hr)).headOption
  }
  /**
    * Get all heaplets from pre and post satisfying a relation
    */
  def findAllMatchingHeaplets(pl: Heaplet => Boolean,
                           pr: (Heaplet, Heaplet) => Boolean,
                           pre: SFormula,
                           post: SFormula): Seq[(Heaplet, Heaplet)] = {
    for {hl <- pre.chunks if pl(hl)
         hr <- post.chunks if pr(hl, hr)} yield (hl, hr)
  }

  /**
    * Are two heaplets both points-to with the same LHS?
    */
  def sameLhs(hl: Heaplet): Heaplet => Boolean = hr => {
    hl match {
      case PointsTo(xl, ol, _, _) => hr match {
        case PointsTo(xr, or, _, _) => xl == xr && ol == or
        case _ => false
      }
      case _ => false
    }
  }

  /**
    * Are two heaplets both points-to with the same RHS?
    */
  def sameRhs(hl: Heaplet): Heaplet => Boolean = hr => {
    hl match {
      case PointsTo(_, _, el, _) => hr match {
        case PointsTo(_, _, er, _) => el == er
        case _ => false
      }
      case _ => false
    }
  }


  /**
    * Find a block satisfying a predicate, and all matching chunks.
    * Returns None if not all chunks are present.
    */
  def findBlockAndChunks(pBlock: Heaplet => Boolean,
                         pPts: Heaplet => Boolean,
                         sigma: SFormula): Option[(Block, Seq[PointsTo])] = {
    findHeaplet(h => h.isInstanceOf[Block] && pBlock(h), sigma) match {
      case None => None
      case Some(h@Block(x@Var(_), sz, _)) =>
        val ptsMb = for (off <- 0 until sz) yield
          findHeaplet(h => sameLhs(PointsTo(x, off, IntConst(0)))(h) && pPts(h), sigma)
//        Some((h, pts.flatten))
        val pts = ptsMb.flatten.map(_.asInstanceOf[PointsTo])
        if (pts.length == sz) Some((h, pts))
        else None
      case Some(h) => throw SynthesisException(s"Not supported: ${h.pp} (${h.getClass.getName})")
    }
  }

  /**
    * Compute cardinality of the symbolic heap as an expression.
    *
    * Returns the size of the non-recursive part as a component.
    */
  def heapCardinality(sigma: SFormula): (Int, Expr) = {
    val heaplets = sigma.chunks
    val ptsCount = heaplets.count {
      _.isInstanceOf[PointsTo]
    }
    val cardinalities = for (SApp(_, _, _, c) <- heaplets) yield c
    if (cardinalities.isEmpty) return (ptsCount, IntConst(ptsCount))

    val res = if (ptsCount == 0) {
      val h :: t = cardinalities
      t.foldLeft(h)((l, r) => BinaryExpr(OpPlus, l, r))
    } else {
      cardinalities.foldLeft(IntConst(ptsCount): Expr)((l, r) => BinaryExpr(OpPlus, l, r))
    }

    (ptsCount, res)
  }

  /**
    * Compare two heaps according to some lexicographic order on instances of the same predicates
    */
  def lexiLT(sigma1: SFormula, sigma2: SFormula, cond: PFormula): Boolean = {
    def lexiOrd(cardPairs: List[(Expr, Expr)]): Expr =
      cardPairs.foldRight(eFalse)((e, res) =>
        BinaryExpr(OpOr, BinaryExpr(OpLt, e._1, e._2), BinaryExpr(OpAnd, BinaryExpr(OpEq, e._1, e._2), res)))

    val cardSeqs = for {
      preds1 <- sigma1.apps.permutations
      preds2 <- sigma2.apps.permutations
      pairs = preds1.zip(preds2)
      if pairs.forall {case (p1, p2) => p1.pred == p2.pred}
    } yield pairs.map {case (p1, p2) => (p1.card, p2.card)}

    cardSeqs.toList.distinct.exists(ps => SMTSolving.valid(cond ==> lexiOrd(ps)))
  }

  /**
    * Compare two heaps according to their total size
    */
  def totalLT(sigma1: SFormula, sigma2: SFormula, cond: PFormula): Boolean = {
//    val (_, card1) = heapCardinality(sigma1)
//    val (_, card2) = heapCardinality(sigma2)
//    val goal = BinaryExpr(OpLt, card1, card2)
//    val res = SMTSolving.valid(cond ==> goal)
//    res
    true
  }
  
  def getCardinalities(sigma: SFormula) = for (SApp(_, _, _, c) <- sigma.chunks) yield c


  /**
    * Find the set of sub-formulas of `large` that `small` might possibly by unified with.
    */
  def findLargestMatchingHeap(small: SFormula, large: SFormula): Seq[SFormula] = {

    def findMatchingFor(h: Heaplet, stuff: Seq[Heaplet]): Seq[Heaplet] = h match {
      case Block(_, sz, _) => stuff.filter {
        case Block(_, _sz, _) => sz == _sz
        case _ => false
      }
      case PointsTo(_, offset, _, _) =>
        stuff.filter {
          case PointsTo(_, _offset, _, _) => offset == _offset
          case _ => false
        }
      case SApp(pred, args, _, _) => stuff.filter {
        case SApp(_pred, _args, _, _) =>
          _pred == pred && args.length == _args.length
        case _ => false
      }
    }

    def goFind(lil: List[Heaplet], larg: List[Heaplet], acc: List[List[Heaplet]]): List[List[Heaplet]] = lil match {
      case h :: hs => (for {
        h1 <- findMatchingFor(h, larg)
        larg1 = larg.filter(_ != h1)
        acc1 = acc.map(hs1 => h1 :: hs1)
        res <- goFind(hs, larg1, acc1)
      } yield res).toList
      case Nil => acc
    }

    val newTypemap = large.tps ** small.tps
    goFind(small.chunks, large.chunks, List(Nil)).map(SFormula(_, newTypemap))
  }

}

case class SepLogicException(msg: String) extends SSLException("seplog", msg)


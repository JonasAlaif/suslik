package org.tygus.suslik.synthesis.rules

import org.tygus.suslik.language.Expressions._
import org.tygus.suslik.language._
import org.tygus.suslik.language.Statements._
import org.tygus.suslik.logic.Specifications._
import org.tygus.suslik.logic._
import org.tygus.suslik.synthesis.{ExtractHelper, PrependProducer, StmtProducer, SubstVarProducer}
import org.tygus.suslik.report.ProofTrace
import org.tygus.suslik.synthesis.rules.Rules._

/**
  * Operational rules emit statement that operate of flat parts of the heap.
  * @author Nadia Polikarpova, Ilya Sergey
  */

object OperationalRules extends SepLogicUtils with RuleUtils {

  val exceptionQualifier: String = "rule-operational"

  import Statements._

  /*
  Write rule: create a new write from where it's possible

  Γ ; {φ ; x.f -> l' * P} ; {ψ ; x.f -> l' * Q} ---> S   GV(l) = GV(l') = Ø
  ------------------------------------------------------------------------- [write]
  Γ ; {φ ; x.f -> l * P} ; {ψ ; x.f -> l' * Q} ---> *x.f := l' ; S

  */
  var toggle = 0
  abstract class WriteAbstract extends SynthesisRule with GeneratesCode {

    override def toString: Ident = "Write"

    def apply(goal: Goal): Seq[RuleResult] = {
      val pre = goal.pre
      val post = goal.post

      // Heaplets have no ghosts
      def noGhosts: Heaplet => Boolean = {
        case PointsTo(x@Var(_), _, e, _) => !goal.isGhost(x) && e.vars.forall(v => !goal.isGhost(v))
        case _ => false
      }
      def sameType: (Heaplet, Heaplet) => Boolean = {
        case (hl@PointsTo(x@Var(_), _, _, _), hr@PointsTo(y@Var(_), _, _, _)) => {
          val st = goal.pre.sigma.tps.get(x) == goal.post.sigma.tps.get(y)
          //println("Typing: " + hl + ": " + goal.pre.sigma.tps.get(x) + " vs " + hr + ": " + goal.post.sigma.tps.get(y) + " //Context, pre: " + goal.pre.sigma + " post: " + goal.post.sigma)
          //if (!st) println("NOT SAME TYPE: " + hl + " vs " + hr)
          st
        }
        case _ => false
      }

      // When do two heaplets match
      def isMatch(hl: Heaplet, hr: Heaplet) = sameLhs(hl)(hr) && !sameRhs(hl)(hr) && noGhosts(hr) && sameType(hl, hr)

      // This is a simple focusing optimization:
      // since in the flat phase all pairs of heaplets must go,
      // we are only working on the first heaplet in the post (and its matching heaplet in the pre)
      //val firstHeaplet = SFormula(goal.post.sigma.chunks.take(1))
      toggle += 1
      findAllMatchingHeaplets(_ => true, isMatch, goal.pre.sigma, goal.post.sigma).flatMap {
        case (hl@PointsTo(x@Var(_), offset, _, p1), hr@PointsTo(_, _, e2, p2)) =>
          val newPre = Assertion(pre.phi, goal.pre.sigma - hl)
          val newPost = Assertion(post.phi && (p1 |=| eMut) && (p2 |=| eMut), goal.post.sigma - hr)
          //println(toggle + ": Trying *(" + x + "+" + offset + ") = " + e2)
          val subGoal = goal.spawnChild(newPre, newPost, typedProgramVars = goal.typedProgramVars.filter(pv => {
              val cnt = !e2.vars.contains(pv._1)
              //println(cnt + ": FV " + pv)
              cnt
          }))
          //val subGoal = goal.spawnChild(newPre, newPost, programVars = goal.programVars.filter(!e2.vars.contains(_)))
          //val subGoal = goal.spawnChild(newPre, newPost)
          val kont: StmtProducer = PrependProducer(Store(x, offset, e2)) >> ExtractHelper(goal)

          ProofTrace.current.add(ProofTrace.DerivationTrail(goal, Seq(subGoal), this,
            Map("to" -> x.pp, "offset" -> offset.toString, "value" -> e2.pp)))
          List(RuleResult(List(subGoal), kont, this, goal))
        case (hl, hr) =>
          ruleAssert(assertion = false, s"Write rule matched unexpected heaplets ${hl.pp} and ${hr.pp}")
          None
      }
    }

  }

  object WriteRule extends WriteAbstract with InvertibleRule

  object WriteSimple extends WriteAbstract

  /*
  Read rule: create a fresh typed read

        y is fresh   Γ,y ; [y/A]{φ ; x -> A * P} ; [y/A]{ψ ; Q} ---> S
      ---------------------------------------------------------------- [read]
             Γ ; {φ ; x.f -> A * P} ; {ψ ; Q} ---> let y := *x.f ; S
  */
  object ReadRule extends SynthesisRule with GeneratesCode with InvertibleRule {

    override def toString: Ident = "Read"

    def apply(goal: Goal): Seq[RuleResult] = {
      val phi = goal.pre.phi
      val sigma = goal.pre.sigma

      def isGhostPoints: Heaplet => Boolean = {
        case PointsTo(x@Var(_), _, e, _) =>
           !goal.isGhost(x) && e.vars.intersect(goal.ghosts).nonEmpty
        case _ => false
      }

      findHeaplet(isGhostPoints, goal.pre.sigma) match {
        case None => Nil
          // TUTORIAL:
        // case Some(pts@PointsTo(x@Var(_), offset, v@Var(name), p)) =>
        //   val y = freshVar(goal.vars, name)
        //   val tpy = v.getType(goal.gamma).get
        //   val subGoal = goal.spawnChild(pre = goal.pre.subst(v, y),
        //     post = goal.post.subst(v, y),
        //     gamma = goal.gamma + (y -> tpy),
        //     programVars = y :: goal.programVars)
        //   val kont: StmtProducer = PrependProducer(Load(y, tpy, x, offset)) >> ExtractHelper(goal)

        //   ProofTrace.current.add(ProofTrace.DerivationTrail(goal, Seq(subGoal), this,
        //     Map("to" -> y.pp, "from" -> x.pp, "offset" -> offset.toString)))

        //   List(RuleResult(List(subGoal), kont, this, goal))
        case Some(pts@PointsTo(x@Var(_), offset, e, p)) =>
          val y = freshVar(goal.vars, e.pp)
          val tpy = e.getType(goal.gamma).get
          val newPhi = phi && (y |=| e)
          val tp = goal.pre.sigma.tps.get(e)
          //println("Got type of " + e + " is " + tp + " in tpenv " + goal.pre.sigma.tps.type_map)
          val newVal = if (tp.get._1.length == 0 && (tp.get._2 == "int" || tp.get._2 == "bool")) y else IntConst(666)
          val newSigma = (sigma - pts) ** SFormula(List(PointsTo(x, offset, newVal, p)), TypeMap(Map(y.name -> tp.get)))
          val subGoal = goal.spawnChild(pre = Assertion(newPhi, newSigma),
                                        gamma = goal.gamma + (y -> tpy),
                                        typedProgramVars = (y, tp) :: goal.typedProgramVars)
          val kont: StmtProducer = e match {
            case a:Var => SubstVarProducer(a, y) >> PrependProducer(Load(y, tp, tpy, x, offset)) >> ExtractHelper(goal)
            case _ => PrependProducer(Load(y, tp, tpy, x, offset)) >> ExtractHelper(goal)
          }
          List(RuleResult(List(subGoal), kont, this, goal))
        case Some(h) =>
          ruleAssert(false, s"Read rule matched unexpected heaplet ${h.pp}")
          Nil
      }
    }
  }

  /*
  Alloc rule: allocate memory for an existential block

           X ∈ GV(post) / GV (pre)        y, Ai fresh
         Γ ; {φ ; y -> (A0 .. An) * P} ; {ψ ; [y/X]Q} ---> S
     -------------------------------------------------------------- [alloc]
     Γ ; {φ ; P} ; {ψ ; block(X, n) * Q} ---> let y = malloc(n); S
  */
  object AllocRule extends SynthesisRule with GeneratesCode {
    override def toString: Ident = "Alloc"

    val MallocInitVal = 666

    def findTargetHeaplets(goal: Goal): Option[(Block, Seq[Heaplet])] = {
      def isExistBlock: Heaplet => Boolean = {
        case Block(x@Var(_), _, _) => goal.isExistential(x)
        case _ => false
      }

      findBlockAndChunks(isExistBlock, _ => true, goal.post.sigma)
    }

    def apply(goal: Goal): Seq[RuleResult] = {

      val pre = goal.pre
      val post = goal.post

      findTargetHeaplets(goal) match {
        case None => Nil
        case Some((Block(x@Var(_), sz, _), _)) =>
          val y = freshVar(goal.vars, x.name)
          val tp = post.sigma.tps.get(x)
          val tpy = LocType

          val freshChunks = for {
            off <- 0 until sz
          } yield PointsTo(y, off, IntConst(MallocInitVal))
          val freshBlock = Block(x, sz).subst(x, y)
          val newPre = Assertion(pre.phi, pre.sigma ** SFormula(freshBlock :: freshChunks.toList, TypeMap(Map(y.name -> goal.post.sigma.tps.get(x).get))))

          val subGoal = goal.spawnChild(newPre,
                                        post.subst(x, y),
                                        gamma = goal.gamma + (y -> tpy),
                                        typedProgramVars = (y, tp) :: goal.typedProgramVars)
          val kont: StmtProducer = SubstVarProducer(x, y) >> PrependProducer(Malloc(y, tp, tpy, sz)) >> ExtractHelper(goal)
          List(RuleResult(List(subGoal), kont, this, goal))
        case _ => Nil
      }
    }

  }

  /*
  Free rule: free a non-ghost block from the pre-state

                     Γ ; {φ ; P} ; {ψ ; Q} ---> S     GV(li) = Ø
   ------------------------------------------------------------------------ [free]
   Γ ; {φ ; block(x, n) * x -> (l1 .. ln) * P} ; { ψ ; Q } ---> free(x); S
*/
  object FreeRule extends SynthesisRule with GeneratesCode {

    override def toString: Ident = "Free"

    def findTargetHeaplets(goal: Goal): Option[(Block, Seq[PointsTo])] = {
      // Heaplets have no ghosts
      def noGhosts(h: Heaplet): Boolean = h.vars.forall(v => goal.isProgramVar(v))

      findBlockAndChunks(noGhosts, _ => true, goal.pre.sigma)
    }

    def apply(goal: Goal): Seq[RuleResult] = {
      val pre = goal.pre
      val post = goal.post

      findTargetHeaplets(goal) match {
        case None => Nil
        case Some((h@Block(x@Var(_), _, p), pts)) =>
          val newPre = Assertion(pre.phi, pre.sigma - h - SFormula(pts.toList, TypeMap()))
          val newPurePost = post.phi && (p |=| eMut) && PFormula(pts.map(_.perm |=| eMut).toSet)
          val newPost = Assertion(newPurePost, post.sigma)

          val subGoal = goal.spawnChild(newPre, newPost)
          val kont: StmtProducer = PrependProducer(Free(x)) >> ExtractHelper(goal)

          List(RuleResult(List(subGoal), kont, this, goal))
        case Some(_) => Nil
      }
    }

  }

}
package org.tygus.suslik.logic

import org.tygus.suslik.LanguageUtils
import org.tygus.suslik.language.Expressions._
import org.tygus.suslik.language.Statements._
import org.tygus.suslik.language._

import scala.Ordering.Implicits._
import org.tygus.suslik.synthesis.rules.Rules
import org.tygus.suslik.synthesis.rules.LogicalRules
import org.tygus.suslik.synthesis.rules.RuslikUnfoldingRules
import org.tygus.suslik.synthesis.rules.UnificationRules

object Specifications extends SepLogicUtils {

  case class Assertion(phi: PFormula, sigma: SFormula) extends HasExpressions[Assertion]
    with PureLogicUtils {

    def pp: String = if (phi.conjuncts.isEmpty) s"{${sigma.pp}}" else s"{${phi.pp} ; ${sigma.pp}}"

    // Collect arbitrary expressions
    def collect[R <: Expr](p: Expr => Boolean): Set[R] =
      phi.collect(p) ++ sigma.collect(p)

    def hasPredicates: Boolean = sigma.chunks.exists(_.isInstanceOf[SApp])

    def getPredicates(p: SApp => Boolean): List[SApp] =
      for (s@SApp(_, _, _, _) <- sigma.chunks if p(s)) yield s

    def hasBlocks: Boolean = sigma.chunks.exists(_.isInstanceOf[Block])

    // Difference between two assertions
    def -(other: Assertion): Assertion = Assertion(PFormula(phi.conjuncts -- other.phi.conjuncts), sigma - other.sigma)

    def subst(s: Map[Var, Expr]): Assertion = if (s.isEmpty) this else Assertion(phi.subst(s), sigma.subst(s))
    def setTagAndRef(h: RApp, cycPreds: PredicateCycles): Assertion = Assertion(phi, sigma.setTagAndRef(h, cycPreds))
    def results(progVars: Set[Var]): Set[Var] = phi.collect[NoExists](_.isInstanceOf[NoExists]).flatMap(_.vars).filter(!progVars(_)) ++
      sigma.sigRapps.filter(r => !r.isBorrow || !r.ref.head.beenAddedToPost).map(_.field)

    def resUnord(progVars: Seq[Var]): FnResList = FnResList(this.results(progVars.toSet))
    def resOrd(progVars: Seq[Var]): FnResList = FnResList(this.results(progVars.toSet).toSeq)

    /**
      * @param takenNames  -- names that are already taken
      * @param globalNames -- variables that shouldn't be renamed
      * @return
      */
    def refresh(takenNames: Set[Var], globalNames: Set[Var]): (Assertion, SubstVar) = {
      val varsToRename = (vars -- globalNames).toList
      val freshSubst = refreshVars(varsToRename, takenNames ++ globalNames)
      (this.subst(freshSubst), freshSubst)
    }

    def ghosts(params: Set[Var]): Set[Var] = this.vars -- params

    def resolve(gamma: Gamma, env: Environment): Option[Gamma] = {
      phi.resolve(gamma) match {
        case None => throw SepLogicException(s"Resolution error in phi: ${phi.pp}")
        case Some(gamma1) => sigma.resolve(gamma1, env) match {
          case None => throw SepLogicException(s"Resolution error in sigma: ${sigma.pp}")
          case Some(gamma2) => Some(gamma2)
        }
      }
    }

    def resolveOverloading(gamma: Gamma): Assertion = {
      this.copy(phi = toFormula(simplify(phi.toExpr.resolveOverloading(gamma))),
        sigma = sigma.resolveOverloading(gamma))
    }

    // Size of the assertion (in AST nodes)
    def size: Int = phi.size + sigma.size

    def cost(predicates: PredicateEnv, cycles: PredicateCycles): Int = sigma.cost(predicates, cycles)
    def postCost(preBrrws: List[RApp]): Int = sigma.postCost(preBrrws)
    def wrapInAE: Assertion = Assertion(this.phi, this.sigma.wrapInAE)
  }

  /**
    * Spatial pre-post pair; used to determine independence of rule applications.
    */
  case class Footprint(pre: Assertion, post: Assertion) {
    def -(other: Footprint): Footprint = Footprint(pre - other.pre, post - other.post)
  }

  /**
    * A label uniquely identifies a goal within a derivation tree (but not among alternative derivations!)
    * Here depths represents how deep we should go down a linear segment of a derivation tree
    * and children represents which branch to take at each fork.
    * For example, a label ([2, 1], [0]) means go 2 steps down from the root, take 0-th child, then go 1 more step down.
    * This label is pretty-printed as "2-0.1"
    */
  case class GoalLabel(depths: List[Int], children: List[Int]) extends PrettyPrinting with Ordered[GoalLabel]  {
    override def pp: String = {
      val d :: ds = depths.reverse
      d.toString ++ children.reverse.zip(ds).map(x => "-" + x._1.toString + "." + x._2.toString).mkString
    }

    private def toList: List[Int] = (List(depths.head) ++ children.zip(depths.tail).flatMap {case (i, j) => List(i, j)}).reverse

    def compare(that: GoalLabel): Int = implicitly[Ordering[List[Int]]].compare(toList, that.toList)

    def bumpUp(childId: Option[Int]): GoalLabel = {
      childId match {
        case None => {
          // Derivation is not branching: simply increase the latest depth
          val x :: xs = depths
          this.copy(depths = (x + 1) :: xs)
        }
        case Some(c) =>
          // Derivation is branching: record which branch we are taking and reset depth
          GoalLabel(0 :: depths, c :: children)
      }
    }
  }

  // Newly added to pre (e.g. by Call) can still be closed
  case class UnfoldConstraints(preNoncyc: Int = 0, // Of all non-cyc rapps
                               preCyc: Int = 0, // Of all cyc rapps
                               postNoncyc: Int = 0, // Of all non-cyc owneds
                               postCyc: Int = 0, // Of all cyc owneds
                               haveClosed: Boolean = false,
    ) {
      def getPre(g: Goal): (List[RApp], List[RApp]) =
        g.pre.sigma.rapps.filter(r =>
          !r.priv &&
          !r.isOpaque(g.env.predicates) &&
          (!r.isPrim(g.env.predicates) || r.ref.length >= 2) &&
          r.tag.unrolls < g.env.config.maxOpenDepth
        ).partition(r => g.env.predicateCycles(r.pred))
      // Borrow or not
      def canUnfoldPre(g: Goal): List[(RApp, UnfoldConstraints, Boolean)] = {
        val (cyc, non) = getPre(g)
        if (non.length > preNoncyc)
          non.drop(preNoncyc).zipWithIndex.map(ri => (ri._1, this.copy(preNoncyc = this.preNoncyc + ri._2), false))
        else cyc.drop(preCyc).zipWithIndex.map(ri => (ri._1, this.copy(
          // Can no longer open non-cyclic
            preNoncyc = non.length,
            preCyc = this.preCyc + ri._2
          ), true)
        )
      }
      // Only owneds
      def canUnfoldPost(g: Goal): List[(RApp, UnfoldConstraints)] = {
        val owneds = g.post.sigma.owneds.filter(!_.isOpaque(g.env.predicates))
        val (cyc, non) = owneds.partition(r => g.env.predicateCycles(r.pred))
        if (non.length > postNoncyc)
          non.drop(postNoncyc).zipWithIndex.map(ri =>
            // Optimization: once closing non-cyclic cannot open non-cyclic
            // (ri._1, this.copy(postNoncyc = this.postNoncyc + ri._2).blockNoncycPre(g))
            (ri._1, this.copy(postNoncyc = this.postNoncyc + ri._2).blockAllPre(g))
          )
        else cyc.drop(postCyc).zipWithIndex.map(ri => (ri._1, this.copy(
          // Can no longer close non-cyclic
            postNoncyc = non.length,
            postCyc = this.postCyc + ri._2
          // Optimization: once closing cyclic cannot open
          ).blockAllPre(g))
        )
      }
      def blockNoncycPre(g: Goal): UnfoldConstraints =
        this.copy(preNoncyc = getPre(g)._2.length)
      def blockAllPre(g: Goal): UnfoldConstraints =
        this.copy(preNoncyc = getPre(g)._2.length, preCyc = getPre(g)._1.length, haveClosed = true)

      def nonBlockedPre(g: Goal): List[RApp] =
        getPre(g)._2.drop(preNoncyc) ++ getPre(g)._1.drop(preCyc)
  }

  /**
    * Main class for contextual Hoare-style specifications
    */
  case class Goal(pre: Assertion,
                  post: Assertion,
                  constraints: UnfoldConstraints, // if I unfold the 2nd SApp, I shouldn't be unfolding 0 or 1 in the future
                  gamma: Gamma, // types of all variables (program, universal, and existential)
                  programVars: List[Var], // program-level variables
                  universalGhosts: Set[Var], // universally quantified ghost variables
                  fname: String, // top-level function name
                  label: GoalLabel, // unique id within the derivation
                  parent: Option[Goal], // parent goal in the derivation
                  env: Environment, // predicates and components
                  sketch: Statement, // sketch
                  callGoal: Option[SuspendedCallGoal],
                  rulesApplied: List[Rules.SynthesisRule],
                  hasProgressed: Boolean,
                  isCompanionNB: Boolean,
                  maxPrevCost: Int = 0,
                  extraCost: Int = 0
                 )

    extends PrettyPrinting with PureLogicUtils {

    val uid: String = LanguageUtils.getTotallyFreshName("goal")

    override def pp: String = {
      def postWithCall: String = {
        val actualCG = callGoal.get.applySubstitution
        s"${post.pp.init} ** ...}\n${actualCG.call.pp}${actualCG.calleePost.pp.init} ** ...}\n...\n${actualCG.callerPost.pp}"
      }

//      s"${label.pp}\n" +
      s"${programVars.map { v => s"${getType(v).pp} ${v.pp}" }.mkString(", ")} " +
        s"[${universalGhosts.map { v => s"${getType(v).pp} ${v.pp}" }.mkString(", ")}]" +
        s"[${existentials.map { v => s"${getType(v).pp} ${v.pp}" }.mkString(", ")}] |-\n" +
        s"${pre.pp}\n${sketch.pp}" +
        (if (callGoal.isEmpty) post.pp else postWithCall)
    }

    lazy val splitPost: (PFormula, PFormula) = {
      val (ex, uni) = post.phi.conjuncts.partition(p => p.vars.exists(this.isExistential))
      (PFormula(uni), PFormula(ex))
    }

    def universalPost: PFormula = splitPost._1

    // Ancestors of this goal in the derivation (root last)
    lazy val ancestors: List[Goal] = parent match {
      case None => Nil
      case Some(p) => p :: p.ancestors
    }

    def ancestorWithLabel(l: GoalLabel): Option[Goal] = ancestors.find(_.label == l)

    // Companion candidates for this goal:
    // look at ancestors before progress was last made, only keep those with different heap profiles
    def companionCandidates: List[(Goal, Int)] = {
      val currRapps = this.pre.sigma.rapps.filter(!_.hasBlocker)
      var matchedWith = currRapps.map(_.field).toSet
      var recursions = 0
      val allCands = ancestors.filter(_.canBeCompanion).flatMap(g => {
        val unmatched = g.pre.sigma.rapps.filter(old => !matchedWith(old.field))
        matchedWith = matchedWith ++ unmatched.map(_.field)
        val newRecs = unmatched.filter(old => {
          currRapps.exists(curr => {
            curr.pred == old.pred && curr.ref.length == old.ref.length && curr.field.name.endsWith(old.field.name)
          })
        })
        recursions += newRecs.length
        if (newRecs.length > 0) Some(g, recursions) else None
      }).reverse
      if (env.config.auxAbduction) allCands else allCands.take(1)
  }

    // Turn this goal into a helper function specification
    def toFunSpec: FunSpec = {
      val name = if (this.isTopLevel) this.fname else this.fname + "_" + this.rulesApplied.length
      val varDecl = this.ghosts.toList.map(v => (v, getType(v))) // Also remember types for non-program vars
      val rustParams = this.pre.sigma.toFormals
      FunSpec(name, None, rustParams, Results(this.rets),
        Assertion(this.pre.phi, this.pre.sigma.toCallGoal(false)),
        Assertion(this.post.phi && this.post.sigma.toFuts(this.gamma)
          , this.post.sigma.toCallGoal(true)), varDecl)
    }

    def toFootprint: Footprint = Footprint(pre, post)

    def spawnChild(pre: Assertion = this.pre,
                   post: Assertion = this.post,
                   fut_subst: Subst = Map.empty,
                   constraints: UnfoldConstraints = this.constraints,
                   gamma: Gamma = this.gamma,
                   programVars: List[Var] = this.programVars,
                   childId: Option[Int] = None,
                   env: Environment = this.env,
                   sketch: Statement = this.sketch,
                   callGoal: Option[SuspendedCallGoal] = this.callGoal,
                   hasProgressed: Boolean = false,
                   isCompanionNB: Boolean = false,
                   extraCost: Int = 0)(implicit rule: Rules.SynthesisRule): Goal = {

      // Resolve types
      val gammaFinal = resolvePrePost(gamma, env, pre, post)

      // Sort heaplets from old to new and simplify pure parts
      val preSimple = Assertion(simplify(pre.phi), pre.sigma).subst(fut_subst)
      val postSimple = Assertion(simplify(post.phi), post.sigma).subst(fut_subst)
      val newCallGoal = if (fut_subst.isEmpty) callGoal else callGoal.map(_.updateSubstitution(fut_subst))
//      val usedVars = preSimple.vars ++ postSimple.vars ++ programVars.toSet ++
//        callGoal.map(cg => cg.calleePost.vars ++ cg.callerPost.vars).getOrElse(Set())
//      val newGamma = gammaFinal.filterKeys(usedVars.contains)
//      val newUniversalGhosts = this.universalGhosts.intersect(usedVars) ++ preSimple.vars -- programVars
      val newUniversalGhosts = this.universalGhosts ++ preSimple.vars -- programVars -- preSimple.alwaysExistsVars

      Goal(preSimple, postSimple, constraints,
        gammaFinal, programVars, newUniversalGhosts,
        this.fname, this.label.bumpUp(childId), Some(this), env, sketch,
        newCallGoal, rule :: rulesApplied, hasProgressed, isCompanionNB,
        this.cost max this.maxPrevCost, extraCost)
    }

    // Goal that is eagerly recognized by the search as unsolvable
    def unsolvableChild: Goal = spawnChild(post = Assertion(pFalse, emp))(LogicalRules.Inconsistency)

    def onExpiries: Set[OnExpiry] = pre.onExpiries ++ post.onExpiries

    // Is this goal unsolvable and should be discarded?
    def isUnsolvable: Boolean = post.phi == pFalse

    // Is this goal very tricky to solve (TODO: think about this more)
    def isProbablyUnsolvable: Boolean =
      // If there is a universal ghost in the post which can never be loaded
      // TODO: Might not be complete in all cases
      post.phi.vars.exists(v =>
        // Cannot possibly get it as a PV
        !(pre.vars ++ programVars).contains(v) &&
        // This doesn't work since we might have { x: Enum(len) }{ len+1 == lenR+1 res: Enum(lenR) }
        // with x not allowed to be opened anymore, but can still be solved by unif
        // !possiblyProgramVars.contains(v) &&

        // Will need to get it as a PV
        universalGhosts.contains(v))

    def borrowsMatch: Boolean = pre.sigma.borrows.forall(b => !b.ref.head.beenAddedToPost || post.sigma.borrows.exists(_.field == b.field))
    def noBlockeds: Boolean = pre.sigma.borrows.forall(b => !b.hasBlocker)
    // Cannot be a companion if there are outstanding non-expired borrows
    def canBeCompanion: Boolean = borrowsMatch && noBlockeds
    def isCompanion: Boolean = isCompanionNB && canBeCompanion

    def isTopLevel: Boolean = label == topLabel || rulesApplied.forall(r =>
      r == RuslikUnfoldingRules.AddToPost ||
      r == RuslikUnfoldingRules.CopyOut ||
      r == LogicalRules.SubstLeft ||
      r == UnificationRules.SubstRight
    )

    def getPredicates(p: SApp => Boolean): Seq[SApp] = pre.getPredicates(p) ++ post.getPredicates(p)

    def hasPredicates(p: SApp => Boolean = _ => true): Boolean = getPredicates(p).nonEmpty

    def hasBlocks: Boolean = pre.hasBlocks || post.hasBlocks

    def hasExistentialPointers: Boolean = post.sigma.chunks.exists {
      case PointsTo(x@Var(_), _, _) => isExistential(x)
      case _ => false
    }

    // If the entire RApp is FULLY existential (fnSpec is existential and unconstrained by phi)
    // Such RApps should not be written to and should be expired eagerly
    def isRAppExistential(r: RApp): Boolean = !r.isWriteableRef(existentials) ||
      // Might as well expire without write if we have no choice; can write to it after expiry if we want to
      // since all the fields will still be there (unlike if we did have an enum)
      (r.ref.length <= 1 && !this.env.predicates(r.pred).isPrim && this.env.predicates(r.pred).clauses.length <= 1) ||
      (r.fnSpec.filter(_.getType(this.gamma).get != LifetimeType).forall(a => {
        if (a.onExpiries.size > 0) return false
        val v = if (a.isInstanceOf[Var]) a.asInstanceOf[Var]
          else if (a.isInstanceOf[AlwaysExistsVar]) a.asInstanceOf[AlwaysExistsVar].v
          else return false
        val phiVars = post.phi.vars ++ pre.phi.vars
        existentials(v) && !phiVars(v)
      }) && !post.onExpiries.exists(oe =>
        oe.field == r.field && !oe.futs.head && oe.post.get
      ))
    def hasPotentialReborrows(r: RApp): Boolean = r.canBeBlocked && this.post.sigma.potentialTgtLfts(r.ref.head.lft)
    def potentialReborrows(r: RApp): List[(RApp, ExprSubst)] = post.sigma.borrows.flatMap(b => r.reborrow(b, this.pre.phi.outlivesRels).map((b, _)))

    // All variables this goal has ever used
    def vars: Set[Var] = gamma.keySet

    // All universally-quantified variables this goal has ever used
    def allUniversals: Set[Var] = universalGhosts ++ programVars

    // All universally-quantified variables this goal has ever used
    def possiblyProgramVars: Set[Var] = constraints.nonBlockedPre(this).flatMap(_.vars).toSet ++ programVars

    // Variables currently used only in specs
    def ghosts: Set[Var] = pre.vars ++ post.vars -- programVars

    // Variables used in the suspended call (if it exists)
    private def callVars: Set[Var] = Set()//callGoal.map(_.actualCall.args.flatMap(_.vars).toSet).getOrElse(Set())

    // Currently used ghosts that appear only in the postcondition (or suspened call)
    def existentials: Set[Var] = post.vars ++ callVars -- allUniversals

    // Determine whether `x` is a ghost variable wrt. given spec and gamma
    def isGhost(x: Var): Boolean = ghosts.contains(x)

    // Determine whether x is in the context
    def isProgramVar(x: Var): Boolean = programVars.contains(x)

    def isExistential(x: Var): Boolean = existentials.contains(x)

    def progLevelPrefix: String = "_prog_"

    // Is x an argument to the call being adbuced
    // and thus must only be unified with program-level expressions?
    def isProgramLevelExistential(x:Var): Boolean = x.name.startsWith(progLevelPrefix) || (
      callGoal match {
        case None => false
        case Some(cg) => cg.call.args.contains(x)
      })

    def getType(x: Var): SSLType = {
      gamma.get(x) match {
        case Some(t) => t
        case None => VoidType
      }
    }

    def substToFormula(sigma: ExprSubst): PFormula = {
      PFormula(sigma.map{ case (e1,e2) => e1 |===| e2}.toSet).resolveOverloading(gamma)
    }

    def splitSubst(sigma: ExprSubst): (Subst, PFormula) = {
      sigma.partition{ case (e, _) => e.isInstanceOf[Var] && isExistential(e.asInstanceOf[Var]) } match {
        case (sub, exprSub) => (sub.map { case (v, e) => (v.asInstanceOf[Var], e)}, substToFormula(exprSub))
      }
    }

    def formals: Formals = pre.sigma.sigRapps.map(_.field).map(v => (v, getType(v)))
    def rets: FnResList = {
      if (this.isTopLevel) post.resOrd(this.programVars) else post.resUnord(this.programVars)
    }

    def depth: Int = ancestors.length

    // Size of the specification in this goal (in AST nodes)
    def specSize: Int = pre.size + post.size

    /**
      * Cost of a goal:
      * for now just the number of heaplets in pre and post
      */
    //    lazy val cost: Int = pre.cost.max(post.cost)
    def cost: Int =
      if (this.extraCost > 0) this.extraCost + (this.maxPrevCost max this.actualCost)
      else this.actualCost
    lazy val actualCost: Int = callGoal match {
        case None => pre.cost(this.env.predicates, this.env.predicateCycles) + post.postCost(pre.sigma.borrows)  // + existentials.size //
        // Add `post.cost` to prevent infinite Closes when abducing call (we allow constructing objects while trying to fn call)
        case Some(cg) => 3 + cg.callerPre.cost(this.env.predicates, this.env.predicateCycles) +
          cg.callerPost.postCost(pre.sigma.borrows) + post.cost(this.env.predicates, this.env.predicateCycles) // + (cg.callerPost.vars -- allUniversals).size //
      }
  }

  def resolvePrePost(gamma0: Gamma, env: Environment, pre: Assertion, post: Assertion): Gamma = {
    pre.resolve(gamma0, env) match {
      case None => throw SepLogicException(s"Resolution error in specification: ${pre.pp}")
      case Some(gamma1) => post.resolve(gamma1, env) match {
        case None => throw SepLogicException(s"Resolution error in specification: ${post.pp}")
        case Some(gamma) => gamma
      }
    }
  }

  // Label of the top-level goal
  def topLabel: GoalLabel = GoalLabel(List(0), List())

  def topLevelGoal(funSpec: FunSpec, env: Environment, sketch: Statement): Goal = {
    val FunSpec(_, _, formals, _, pre, post, var_decl) = funSpec
    topLevelGoal(pre, post, formals, funSpec.clean, env, sketch, var_decl)
  }

  def topLevelGoal(pre: Assertion, post: Assertion, formals: RustFormals, fname: String, env: Environment, sketch: Statement, vars_decl: Formals): Goal = {
    val gamma0 = (formals.map(_._1 -> LocType) ++ vars_decl).toMap // initial environemnt: derived from the formals
    val gamma = resolvePrePost(gamma0, env, pre, post)
    val pre1 = pre.resolveOverloading(gamma)
    val post1 = post.resolveOverloading(gamma)
    val formalNames = formals.map(_._1)
    val ghostUniversals = pre1.vars -- formalNames
    Goal(pre1, post1, UnfoldConstraints(),
      gamma, formalNames, ghostUniversals,
      fname, topLabel, None, env.resolveOverloading(), sketch.resolveOverloading(gamma),
      None, List.empty, hasProgressed = false, isCompanionNB = true, 0, 0)
  }

  /**
    * Stored information necessary to compute call arguments and the goal after call
    * when in call abduction mode
    * @param callerPre precondition of the goal where call abduction started
    * @param callerPost postcondition of the goal where call abduction started
    * @param calleePost postcondition of the companion goal
    * @param call call statement
    */
  case class SuspendedCallGoal(callerPre: Assertion,
                               callerPost: Assertion,
                               calleePost: Assertion,
                               call: Call,
                               companionToFresh: SubstVar,
                               allowedRecursions: Int,
                               hasBorrows: Boolean,
                               freshToActual: Subst = Map.empty) {
    def updateSubstitution(sigma: Subst): SuspendedCallGoal = {
      assertNoOverlap(freshToActual, sigma)
      this.copy(freshToActual = compose(freshToActual, sigma) ++ sigma)
    }

    def applySubstitution: SuspendedCallGoal = {
      val newCalleePost = calleePost.subst(freshToActual)
      val newCall = call.copy(args = call.args.map(_.subst(freshToActual)))
      this.copy(calleePost = newCalleePost, call = newCall)
    }

    def actualCall: Call = call.copy(args = call.args.map(_.subst(freshToActual)))

    def addPostFact(e: Expr): SuspendedCallGoal = this.copy(callerPost = this.callerPost.copy(phi = this.callerPost.phi && e))

    // lazy val cost: Int = calleePost.cost
  }
}



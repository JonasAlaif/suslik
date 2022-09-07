package org.tygus.suslik.synthesis.rules

import org.tygus.suslik.language.Expressions._
import org.tygus.suslik.language.Statements._
import org.tygus.suslik.language.{CardType, Ident}
import org.tygus.suslik.logic.Specifications._
import org.tygus.suslik.logic._
import org.tygus.suslik.logic.smt.SMTSolving
import org.tygus.suslik.report.ProofTrace
import org.tygus.suslik.synthesis.Termination.Transition
import org.tygus.suslik.synthesis._
import org.tygus.suslik.synthesis.rules.Rules._
import org.tygus.suslik.language.LifetimeType
import org.tygus.suslik.language.SSLType

/**
  * Unfolding rules deal with Rust predicates and recursion.
  *
  * @author Jonas Fiala
  */

object RuslikUnfoldingRules extends SepLogicUtils with RuleUtils {
  val exceptionQualifier: String = "rule-unfolding"

  def onExpiryFromParam(param: Var, ip: InductivePredicate, predicates: PredicateEnv): Expr = {
    for (c <- ip.clauses) {
      for (r <- c.asn.sigma.rapps) {
        val idx = r.fnSpec.find(e => e.isInstanceOf[Var] && e.asInstanceOf[Var] == param)
        if (idx.isDefined) return idx.get
      }
    }
    for (c <- ip.clauses) {
      for (BinaryExpr(op, Var(lhs), rhs) <- c.asn.phi.conjuncts
        if (op == OpEq || op == OpSetEq || op == OpBoolEq) && lhs == param.name) {
        return rhs
      }
    }
    println(s"Failed to find `${param.pp}` in ${ip.pp}!")
    ???
  }

  // The returned ip is the non-modified one
  def loadPred(rapp: RApp, vars: Set[Var], predicates: PredicateEnv, isPre: Boolean, onExpiries: Set[OnExpiry], cycPreds: PredicateCycles): (Seq[InductiveClause], Subst, SubstVar, SubstVar, Subst, InductivePredicate) = {
    assert(!rapp.hasBlocker)
    if (rapp.ref.length >= 2) {
      val newRapp = rapp.popRef
      val ic = InductiveClause(None, BoolConst(true), Assertion(PFormula(BoolConst(true)), SFormula(List(newRapp))))
      val ip = InductivePredicate(false, "deref", List.empty, Seq(ic), None)
      (Seq(ic), Map.empty, Map.empty, Map(Var("*") -> newRapp.field), onExpiries.flatMap(_.openOrExpireSub(rapp.field, newRapp.field, !isPre)).toMap, ip)
    } else {
      val ip = predicates(rapp.pred)
      assert(ip.params.length == rapp.fnSpec.length)
      val args_subst = ip.params.map(_._1).zip(rapp.fnSpec).toMap
      // Functional values should never accidentally alias (an existential RApp in the post should remain so)
      val prePostUniq = if (isPre) "O" else "F"
      val existentials_subst = ip.existentials.map(e => e -> Var(e.name + "_" + rapp.field.name + prePostUniq)).toMap
      // Fields should always alias (so that refs match up in pre/post)
      val fields_subst = ip.fields.map(e =>
        e -> (if (e.name == "_666") Var("bx_" + rapp.field.name) else Var(e.name + "_" + rapp.field.name))
      ).toMap
      val subst = args_subst ++ existentials_subst ++ fields_subst
      val newIp = ip.clauses.map(c =>
        InductiveClause(
          c.name,
          c.selector.subst(if (rapp.isBorrow && !isPre) existentials_subst else subst),
          c.asn.subst(subst).setTagAndRef(rapp, cycPreds)
        )
      )
      // !isBorrow: any futures will be dealt with by addToPost
      val futures_subst: Subst = if (!rapp.isBorrow) Map.empty
        else if (ip.isPrim || ip.clauses.length == 0) {
          assert(ip.params.length == 1)
          onExpiries.flatMap(_.copyOutSub(rapp.field, ip.params.head._1.subst(subst), !isPre)).toMap
        } else {
          // I should have changed all non-fut onExpiries to the corresponding fields by now
          assert(onExpiries.forall(oe => oe.field != rapp.field || oe.futs.head), "Got onExpiries: " + onExpiries)
          // val params_oe_subst = ip.params.zipWithIndex.filter(_._1._2 != LifetimeType).map(p =>
          //   OnExpiry(Some(!isPre), List(false), rapp.field, p._2, p._1._2).asVar
          //     -> onExpiryFromParam(p._1._1, ip, predicates).subst(subst)
          // ).toMap
          newIp.flatMap(c => {
            val oes = c.asn.onExpiries
            val fields = c.asn.sigma.rapps.map(r => r.field -> r.fnSpec.filter(!_.isInstanceOf[Named])).toMap
            oes.flatMap(_.openOrExpirePredSub(fields, !isPre))
          }).toMap
        }

      (newIp, args_subst, existentials_subst, fields_subst, futures_subst, ip)
    }
  }

  def loadPrimPred(rapp: RApp, vars: Set[Var], predicates: PredicateEnv, onExpiries: Set[OnExpiry]): (Assertion, Subst) = {
    // There should be no existentials in a primitive pred (so `isPre` is irrelevant)
    val (pred_clauses, _, exists, subst, fut_subst, _) = loadPred(rapp.copy(ref = rapp.ref match { case Nil => Nil; case r :: _ => List(r) }), vars, predicates, true, onExpiries, Set.empty)
    assert(subst.isEmpty)
    assert(exists.isEmpty)
    assert(pred_clauses.length == 1 && pred_clauses.head.selector == BoolConst(true))
    (pred_clauses.head.asn, fut_subst)
  }

  /*
  Copy out rule: load in a primitive value
   */
  object CopyOut extends SynthesisRule with GeneratesCode with InvertibleRule {
    override def toString: Ident = "CopyOut"

    def apply(goal: Goal): Seq[RuleResult] = {
      // Prevent repeatedly copying out from borrows
      def loadVars(rapp: RApp): Seq[Var] =
        for { v@Var(_) <- rapp.fnSpec; if !goal.programVars.contains(v) } yield v
      // Take first prim, we will unfold all anyway
      val prims = goal.pre.sigma.prims(goal.env.predicates).filter(h => !h.priv && !h.hasBlocker && !loadVars(h).isEmpty)
      if (prims.length == 0) return Seq()
      val prim = prims.head
      val (asn, fut_subst) = loadPrimPred(prim, goal.vars, goal.env.predicates, goal.onExpiries)
      val newVars = loadVars(prim)
      val extraPhi = asn.phi - PFormula(asn.phi.collect[Expr](_.isInstanceOf[NoExists]))
      val newGoal = goal.spawnChild(
        Assertion(goal.pre.phi && extraPhi, goal.pre.sigma),
        fut_subst = fut_subst,
        programVars = goal.programVars ++ newVars
      )
      assert(newVars.length == 1)
      val field = prim.ref.foldLeft[Expr](prim.field)((acc, _) => UnaryExpr(OpDeRef, acc))
      val kont = CrossFnSubstProducer(newVars.head, field)
      Seq(RuleResult(List(newGoal), kont, this, goal))
    }
  }

  /*
  Open rule: unroll a predicate in the pre-state
   */
  object Open extends SynthesisRule with GeneratesCode {

    override def toString: Ident = "Open"

    def apply(goal: Goal): Seq[RuleResult] = {
      for {
        (h, c, isCyc) <- goal.constraints.canUnfoldPre(goal)
        // TODO: these checks are redundant (done in canUnfoldPre)
        if !h.priv && !h.hasBlocker // Must be non-private and non-blocked
        // Only for non-primitive types
        if !h.isPrim(goal.env.predicates) || h.ref.length >= 2
        if h.tag.unrolls < goal.env.config.maxOpenDepth
        (clauses, sbst, fresh_subst, fieldSubst, fut_subst, pred) = loadPred(h, goal.vars, goal.env.predicates, true, goal.onExpiries, goal.env.predicateCycles)
        if clauses.length > 0
      } yield {
        val newGoals = clauses.zipWithIndex.map { case (clause, j) => {
          val newVars = clause.asn.sigma.rapps.map(_.field)
          goal.spawnChild(
            pre = Assertion(goal.pre.phi && clause.asn.phi && clause.selector, goal.pre.sigma ** clause.asn.sigma - h),
            fut_subst = fut_subst,
            constraints = c,
            programVars = goal.programVars ++ newVars,
            childId = Some(j),
            // True since we might satisfy the call termination requirement now
            hasProgressed = true,
            // If we reborrowed cannot be a companion since the borrows won't match up (need to expire first)
            isCompanionNB = !h.isBorrow)
        }}
        val subs = fieldSubst.map{ case (field, var_name) =>
          var_name -> (if (field.name == "*" || field.name == "_666") {
            if (h.isBorrow) UnaryExpr(OpDeRef, UnaryExpr(OpDeRef, h.field)) else UnaryExpr(OpDeRef, h.field)
          } else BinaryExpr(OpField, h.field, Var(field.name.stripPrefix("_"))))
        }.toMap
        val nameSubs = if (h.isBorrow) subs.map(m => m._1 -> UnaryExpr(OpTakeRef(h.ref.head.mut), m._2)) else subs
        val kont = MatchProducer(Results(goal.post.resUnord(goal.programVars)), h.field, pred.clean, fieldSubst, nameSubs, pred.clauses.map(c => c.name -> c.asn.sigma.rapps.filter(!_.priv).map(_.field))) >>
          ExtractHelper(goal)
        RuleResult(newGoals, kont, this, goal)
      }
    }
  }

  /*
  OpenInv rule: unroll a ref predicate in the pre-state
   */
  object OpenInv extends SynthesisRule with GeneratesCode with InvertibleRule {

    override def toString: Ident = "OpenInv"

    def apply(goal: Goal): Seq[RuleResult] = {
      for (h <- goal.pre.sigma.borrows
        if !h.priv && !h.hasBlocker && (!h.isPrim(goal.env.predicates) || h.ref.length >= 2) && h.tag.unrolls < goal.env.config.maxOpenDepth &&
        !goal.post.onExpiries.exists(oe => oe.field == h.field && !oe.post.get && !oe.futs.head) &&
        h.ref.head.beenAddedToPost) {
        val (clauses, sbst, fresh_subst, fieldSubst, fut_subst, pred) = loadPred(h, goal.vars, goal.env.predicates, true, goal.onExpiries, goal.env.predicateCycles)
        if (clauses.length > 0) {
        var counter: Int = 0
        val newGoals = clauses.zipWithIndex.map { case (clause, j) => {
          if (clause.selector != BoolConst(false)) counter += 1
          val newVars = clause.asn.sigma.rapps.map(_.field)
          goal.spawnChild(
            pre = Assertion(goal.pre.phi && clause.asn.phi && clause.selector, goal.pre.sigma ** clause.asn.sigma - h),
            fut_subst = fut_subst,
            programVars = goal.programVars ++ newVars,
            childId = Some(j),
            // True since we might satisfy the call termination requirement now
            hasProgressed = true,
            // If we reborrowed cannot be a companion since the borrows won't match up (need to expire first)
            isCompanionNB = !h.isBorrow)
        }}
        if (counter <= 1) {
        val subs = fieldSubst.map{ case (field, var_name) =>
          var_name -> (if (field.name == "*" || field.name == "_666") {
            if (h.isBorrow) UnaryExpr(OpDeRef, UnaryExpr(OpDeRef, h.field)) else UnaryExpr(OpDeRef, h.field)
          } else BinaryExpr(OpField, h.field, field))
        }.toMap
        val nameSubs = if (h.isBorrow) subs.map(m => m._1 -> UnaryExpr(OpTakeRef(h.ref.head.mut), m._2)) else subs
        // TODO: Why was the `if (m._2.isInstanceOf[UnaryExpr]) m._2 else ...` here?
        // val nSubsRef = if (h.isBorrow) nameSubs.map(m => m._1 -> (if (m._2.isInstanceOf[UnaryExpr]) m._2 else UnaryExpr(OpTakeRef(h.ref.head.mut), m._2))) else nameSubs
        val kont = MatchProducer(Results(goal.post.resUnord(goal.programVars)), h.field, pred.clean, fieldSubst, nameSubs, pred.clauses.map(c => c.name -> c.asn.sigma.rapps.filter(!_.priv).map(_.field))) >>
          ExtractHelper(goal)
        return Seq(RuleResult(newGoals, kont, this, goal))
      }}}
      Seq()
    }
  }

  object AbduceCall extends SynthesisRule {

    override def toString: Ident = "TryCall"

    def apply(goal: Goal): Seq[RuleResult] = {
      val cands = goal.companionCandidates
      val funLabels = cands.map(a => (a.toFunSpec, Some(a.label))) ++ // companions
        goal.env.functions.values.map(f => (f, None)) // components
      for {
        (_f, l) <- funLabels
        (freshSub, f) = _f.refreshAll(goal.vars)

        // Optimization: do not consider f if its pre has predicates that cannot possibly match ours
        if multiSubset(f.pre.sigma.profile.apps, goal.pre.sigma.profile.apps)
        if (goal.env.config.maxCalls :: goal.pre.sigma.callTags).min < goal.env.config.maxCalls
      } yield {
        val newGamma = goal.gamma ++ (f.params ++ f.var_decl).toMap // Add f's (fresh) variables to gamma
        val call = Call(Var(f.clean), f.returns, f.params.map(_._1), l, _f.params.headOption.map(_._1.name == "self").getOrElse(false))
        val calleePostSigma = f.post.sigma.setSAppTags(PTag().incrCalls)
        val callePost = Assertion(f.post.phi, calleePostSigma)
        val suspendedCallGoal = Some(SuspendedCallGoal(goal.pre, goal.post, callePost, call, freshSub))
        val newGoal = goal.spawnChild(post = f.pre, gamma = newGamma, callGoal = suspendedCallGoal)
        val kont: StmtProducer = AbduceCallProducer(f) >> ExtractHelper(goal)

        ProofTrace.current.add(ProofTrace.DerivationTrail(goal, Seq(newGoal), this,
          Map("fun" -> f.name, "args" -> f.params.map(_._1.pp))))

        RuleResult(List(newGoal), kont, this, goal)
      }
    }
  }


  /*
  Close rule: unroll a predicate in the post-state
   */
  object Close extends SynthesisRule {

    override def toString: Ident = "Close"

    def apply(goal: Goal): Seq[RuleResult] = {
      for {
        // TODO: Could potentially be a create-borrow rule as well for local lifetimes
        (h, c) <- goal.constraints.canUnfoldPost(goal)
        // TODO: we might get stuck here
        // (canUnfoldPost only returns non-cyclic, but none of those are unfoldable, so can never get to unfolding non-cyclic)
        if h.tag.unrolls < goal.env.config.maxCloseDepth
        val (clauses, _, fresh_subst, fieldSubst, fut_subst, ip) = loadPred(h, goal.vars, goal.env.predicates, false, goal.onExpiries, goal.env.predicateCycles)
        (InductiveClause(name, selector, asn), idx) <- clauses.zipWithIndex
        if selector != BoolConst(false)
        if asn.sigma.rapps.filter(r => r.priv && !r.field.name.startsWith("disc")).length == 0
      } yield {
        assert(!h.hasBlocker)
        // TODO: hacky way to remove discriminant
        val (noDisc, disc) = asn.sigma.chunks.partition {
          case RApp(true, _, _, _, _, _, _) => false
          case _ => true
        }
        val newPost = Assertion(
          goal.post.phi && asn.phi && selector,
          goal.post.sigma ** SFormula(noDisc) - h
        )
        val construct_args = if (ip.isPrim) {
          assert(h.fnSpec.length == 1)
          var deAE = h.fnSpec(0).collect[AlwaysExistsVar](_.isInstanceOf[AlwaysExistsVar]).map(ae => ae.v -> ae.v).toMap
          Seq(h.field -> h.fnSpec(0).subst(deAE))
        } else {
          val fieldNames = ip.clauses(idx).asn.sigma.rapps.filter(!_.priv).map(_.field)
          val argNames = asn.sigma.rapps.filter(!_.priv).map(_.field)
          assert(fieldNames.length == argNames.length)
          fieldNames.zip(argNames)
        }
        val kont =
          UnfoldProducer(h.toSApp, selector, Assertion(asn.phi, asn.sigma), fresh_subst ++ fieldSubst) >>
          (if (ip.isPrim) SubstProducer(construct_args(0)._1, construct_args(0)._2)
          else AppendProducer(Construct(Some(h.field), ip.clean, name, construct_args))) >>
          ExtractHelper(goal)
        RuleResult(List(goal.spawnChild(post = newPost, fut_subst = fut_subst, constraints = c,
            // Hasn't progressed since we didn't progress toward termination
            // Could be used as a companion, but currently won't since it isn't possible to make progess after closing (no more open)
            hasProgressed = false, isCompanionNB = true)), kont, this, goal)
      }
    }
  }

  /*
  Expire rule: expire a reborrow in the post-state
   */
  abstract class Expire extends SynthesisRule {

    override def toString: Ident = "Expire"

    def filter(r: RApp, goal: Goal): Boolean
    def apply(goal: Goal): Seq[RuleResult] = {
      val preBorrows = goal.pre.sigma.borrows.map(_.field)
      for {
        h <- goal.post.sigma.borrows
        // Expire non-writable borrows eagerly
        if filter(h, goal)
        // Cannot expire existential
        if h.ref.head.beenAddedToPost
        // Cannot expire before reborrowing:
        if !preBorrows.contains(h.field)
        val (clauses, sbst, _, _, fut_subst, _) = loadPred(h, goal.vars, goal.env.predicates, false, goal.onExpiries, goal.env.predicateCycles)
        InductiveClause(name, selector, asn) <- clauses
        // Hacky way to ensure we can only Expire the correct enum variant:
        if selector == BoolConst(true) || {
          val sel = selector.asInstanceOf[BinaryExpr]
          val disc = asn.sigma.rapps.find(d => d.field.name.startsWith("disc")).get
          // if (goal.pre.sigma.rapps.find(_.field == disc.field).isEmpty)
          //   println("Goal " + goal.rulesApplied + " could not find disc " + disc.field.pp + " in " + goal.pre.sigma.pp)
          val pre_disc = goal.pre.sigma.rapps.find(_.field == disc.field).get
          if (pre_disc.fnSpec.length != 1) println("Found: " + pre_disc.pp)
          assert(pre_disc.fnSpec.length == 1)
          pre_disc.fnSpec.head.asInstanceOf[Const] == sel.right
        }
      } yield {
        val blocked = if (h.isUnblockable) asn.sigma.mkUnblockable else asn.sigma
        val selectorEQ = if (selector != BoolConst(true)) {
          val left = selector.asInstanceOf[BinaryExpr].left.asInstanceOf[Var]
          // ArgSubst contains?
          if (sbst.contains(left)) sbst(left) |=| left else BoolConst(true)
        } else BoolConst(true)
        val newPost = Assertion(
          // Assumption: selector will be substituted in (since it's an equality when clauses.length != 1)
          goal.post.phi && asn.phi && selector && selectorEQ,
          goal.post.sigma ** blocked - h
        )
        RuleResult(List(goal.spawnChild(post = newPost, fut_subst = fut_subst,
            // Hasn't progressed since we didn't progress toward termination, but can be companion
            hasProgressed = false, isCompanionNB = true)), IdProducer, this, goal)
      }
    }
  }
  object ExpireNoWrite extends Expire {
    // Can always expire -> ExpireFinal will take the ones we should expire now
    override def filter(r: RApp, goal: Goal): Boolean = true
  }
  object ExpireFinal extends Expire with InvertibleRule {
    override def filter(r: RApp, goal: Goal): Boolean =
      // Don't need to try writing
      goal.isRAppExistential(r) &&
      // Don't need to try reborrowing
      !goal.hasPotentialReborrows(r)
  }

  // i.e. from { 'a >= 'b ; x: &'a mut i32(val_x) } { x: &'a mut i32(FA_val_result)<'tmp> ** result: &'b mut i32(val_result) }
  //        to { 'a >= 'b ; x: &'a mut i32(val_x) } { 'a >= 'b ; x: &'a mut i32(FA_val_result)<'tmp> }
  /*
  Reborrow rule: reborrow in post to unify with post
   */
  object Reborrow extends SynthesisRule {

    override def toString: Ident = "Reborrow"

    def apply(goal: Goal): Seq[RuleResult] = {
      for {
        src <- goal.post.sigma.borrows
        (tgt, sub) <- goal.potentialReborrows(src)
      } yield {
        assert(tgt.ref.head.lft.fa) // Unsupported as of now (how would it happen that we're trying to create a borrow with existential lft - could just kill?)
        val tgtPred = goal.env.predicates(tgt.pred)
        assert(tgtPred.params.length == src.fnSpec.length)
        val fut_subst = goal.onExpiries.flatMap(_.reborrowSub(tgt.field, src.field, tgt.fnSpec)).toMap
        // `src.fnSpec` are existentials, need to bind them to all of the futures
        val exists_bind = if (tgt.ref.head.mut)
          PFormula(src.fnSpec.zipWithIndex.zip(tgtPred.params.map(_._2)).filter(_._2 != LifetimeType).map(p => {
            (OnExpiry(Some(true), true :: List.fill(tgt.ref.length-1)(false), src.field, p._1._2, p._2) |===| p._1._1)
          }).toSet + (tgt.field |===| src.field)).resolveOverloading(goal.gamma)
        else goal.substToFormula(sub)
        val addLftRel = BinaryExpr(OpOutlived, tgt.ref.head.lft, src.ref.head.lft)
        val newPost = Assertion(
          goal.post.phi && exists_bind && addLftRel,
          (goal.post.sigma - tgt - src) ** src.copy(fnSpec = tgt.fnSpec).mkUnblockable
        )
        val kont =
          // We'll get a (tgt.field |===| src.field) subst anyway
          // SubstProducer(tgt.field, src.field) >>
          ExtractHelper(goal)
        RuleResult(List(goal.spawnChild(post = newPost, fut_subst = fut_subst,
            // Hasn't progressed since we didn't progress toward termination, but can be companion
            hasProgressed = false, isCompanionNB = true)), kont, this, goal)
      }
    }
  }

  /*
  Borrow write rule: write to a borrow in the post-state
   */
  object BrrwWrite extends SynthesisRule {

    override def toString: Ident = "BrrwWrite"

    def apply(goal: Goal): Seq[RuleResult] = {
      val post = goal.post
      val env = goal.env

      for {
        brrw <- goal.post.sigma.borrows
        if !goal.isRAppExistential(brrw)
      } yield {
        val newOwned = brrw.copy(field = Var(brrw.field.name + "_NV"), ref = brrw.ref.tail, blocked = None, tag = brrw.tag.copy(calls = 0))
        val newBrrw = brrw.refreshFnSpec(goal.gamma, goal.vars).mkUnblockable
        val newPost = Assertion(post.phi, (post.sigma ** newOwned - brrw) ** newBrrw)

        val fut_subst = goal.onExpiries.flatMap(
          _.writeSub(brrw.field, newOwned.field, newOwned.fnSpec, brrw.fnSpec, true)).toMap

        val kont = AppendProducer(Store(brrw.field, 0, newOwned.field))
        RuleResult(List(goal.spawnChild(post = newPost, fut_subst = fut_subst)), kont, this, goal)
      }
    }
  }

  /*
  Add to post
   */
  object AddToPost extends SynthesisRule with InvertibleRule {
    override def toString: Ident = "AddToPost"

    def apply(goal: Goal): Seq[RuleResult] = {
      val post = goal.post
      val env = goal.env

      val preBrrws = goal.pre.sigma.borrows.filter(!_.ref.head.beenAddedToPost)
      if (preBrrws.length == 0) return Nil
      val preBrrw = preBrrws.head
      val newPreBrrw = preBrrw.copy(ref = preBrrw.ref.head.copy(beenAddedToPost = true) :: preBrrw.ref.tail)
      val newPre = Assertion(goal.pre.phi, (goal.pre.sigma - preBrrw) ** newPreBrrw)

      // Only refresh fnspec if mutable
      val newFnSpec =
        if (newPreBrrw.ref.head.mut) newPreBrrw.refreshFnSpec(goal.gamma, goal.vars, true).fnSpec
        else newPreBrrw.fnSpec
      assert(!newPreBrrw.hasBlocker)
      val newPostBrrw = newPreBrrw.copy(fnSpec = newFnSpec)
      val fut_subst = goal.onExpiries.flatMap(_.toPostSub(newPreBrrw.field, newPreBrrw.fnSpec, newPostBrrw.fnSpec)).toMap
      // println("fut_subst: " + fut_subst)

      val newPost = Assertion(goal.post.phi, goal.post.sigma ** newPostBrrw)
      val newGoal = goal.spawnChild(pre = newPre, post = newPost, fut_subst = fut_subst)//, isCompanionNB = true)
      Seq(RuleResult(List(newGoal), IdProducer, this, goal))
    }
  }

  /*
  Reborrow for calls rule: reborrow in pre to unify with post
   */
  object ReborrowCall extends SynthesisRule {

    override def toString: Ident = "ReborrowCall"

    def apply(goal: Goal): Seq[RuleResult] = {
      if (goal.callGoal.isEmpty) return Nil
      for {
        src <- goal.pre.sigma.borrows
        if src.isBorrow
        tgt <- goal.post.sigma.borrows
        sub <- src.reborrow(tgt, goal.pre.phi.outlivesRels)
      } yield {
        assert(!goal.existentials(src.field) && goal.existentials(tgt.field))
        // TODO:
        assert(src.fnSpec.forall(_.getType(goal.gamma) != LifetimeType))
        val (newPre, fut_subst, newCG) = if (src.ref.head.mut) {
          val newSrc = if (tgt.ref.head.mut) src.refreshFnSpec(goal.gamma, goal.vars) else src
          val newSrcBlck = newSrc.block(tgt.ref.head.lft).setTag(newSrc.tag.incrCalls)
          val newPre = Assertion(
            goal.pre.phi,
            (goal.pre.sigma - src) ** newSrcBlck
          )
          val fut_subst = if (tgt.ref.head.mut) {
              (goal.onExpiries ++ goal.callGoal.get.calleePost.onExpiries).flatMap(
                _.reborrowCallSub(tgt.field, src.field, src.fnSpec, newSrc.fnSpec, goal.vars)
              ).toMap
          } else Map.empty[Var, Expr]
          (
            newPre,
            fut_subst,
            Some(goal.callGoal.get.addPostFact(BinaryExpr(OpOutlived, tgt.ref.head.lft, src.ref.head.lft)))
          )
        } else {
          val newPre = Assertion(goal.pre.phi,
            (goal.pre.sigma - src) ** src.setTag(src.tag.incrCalls)
          )
          val fut_subst = if (tgt.ref.head.lft.name == src.ref.head.lft.name) Map.empty[Var, Expr]
                          else Map(tgt.ref.head.lft.name -> src.ref.head.lft.name)
          (newPre, fut_subst, goal.callGoal)
        }
        // TODO: use?
        // println("\nMade onExpiry: " + src.mkOnExpiry(goal.gamma, Some(false)).pp);
        val phiPost = goal.substToFormula(sub)
        val newPost = Assertion(goal.post.phi && phiPost, goal.post.sigma - tgt)
        // println("Calculating fut_subst for: " + goal.rulesApplied)
        // println("Pre: " + goal.pre.pp)
        // println("Post: " + goal.post.pp)
        // println("Calee Post: " + goal.callGoal.get.calleePost.pp)
        RuleResult(List(goal.spawnChild(
          pre = newPre, post = newPost, fut_subst = fut_subst, callGoal = newCG
        )), IdProducer, this, goal)
      }
    }
  }

  /*
  KillLft: if no ref has this lft then might as well kill it
   */
  object KillLft extends SynthesisRule with InvertibleRule {

    override def toString: Ident = "KillLft"

    def apply(goal: Goal): Seq[RuleResult] = {
      // Should not be used anywhere else (otherwise we'd kill off another RApp - may want to do but not InvertibleRule style)
      val usedLfts = goal.pre.sigma.rapps.flatMap(r => r.fnSpec.flatMap(_.collect[Named](_.isInstanceOf[Named])) ++ r.ref.map(_.lft)).toSet ++
      // Should not have to outlive some other lft
        goal.post.phi.outlivesRels.map(_._2)
      val tryToKill = goal.pre.sigma.rapps.flatMap(_.getBlocker).filter(!_.fa)
      val toKill = tryToKill.find(!usedLfts(_))
      if (toKill.isEmpty) Nil
      else {
        val newGoal = goal.spawnChild(fut_subst = Map(toKill.get.name -> NilLifetime))
        List(RuleResult(List(newGoal), IdProducer, this, goal))
      }
    }
  }

  /*
  Cannot construct: if there is a universal ghost or OE in a MustConstruct (NoExists)
   */
  object CannotConstruct extends SynthesisRule with InvertibleRule {

    override def toString: Ident = "CannotConstruct"

    def apply(goal: Goal): Seq[RuleResult] = {
      if (goal.callGoal.isDefined || !goal.post.sigma.chunks.isEmpty) return Nil
      val existsSat = goal.post.phi.collect[NoExists](_.isInstanceOf[NoExists]).forall(ne =>
        ne.onExpiries.size == 0 && ne.vars.forall(v => !goal.universalGhosts(v))
      )
      if (existsSat) return Nil
      List(RuleResult(List(goal.unsolvableChild), IdProducer, this, goal))
    }
  }
}

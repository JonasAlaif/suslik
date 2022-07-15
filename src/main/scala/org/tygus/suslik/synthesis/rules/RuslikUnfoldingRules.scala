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

  def loadPred(rapp: RApp, vars: Set[Var], predicates: PredicateEnv, isPre: Boolean, onExpiries: Set[OnExpiry]): (Seq[InductiveClause], Subst, SubstVar, SubstVar, Subst) = {
    assert(!(isPre && rapp.hasBlocker))
    if (rapp.ref.length >= 2) {
      val newRapp = rapp.popRef
      val ic = InductiveClause(None, BoolConst(true), Assertion(PFormula(BoolConst(true)), SFormula(List(newRapp))))
      (Seq(ic), Map.empty, Map.empty, Map(Var("*") -> newRapp.field), onExpiries.flatMap(_.openOrExpireSub(rapp.field, newRapp.field, !isPre)).toMap)
    } else {
      val ip = predicates(rapp.pred)
      assert(ip.params.length == rapp.fnSpec.length)
      val args_subst = ip.params.map(_._1).zip(rapp.fnSpec).toMap
      // Functional values should never accidentally alias (an existential RApp in the post should remain so)
      val prePostUniq = if (isPre) "O" else "F"
      val existentials_subst = ip.existentials.map(e => e -> Var(e.name + "_" + rapp.field.name + prePostUniq)).toMap
      // Fields should always alias (so that refs match up in pre/post)
      val fields_subst = ip.fields.map(e => e -> Var(e.name + "_" + rapp.field.name)).toMap
      val subst = args_subst ++ existentials_subst ++ fields_subst
      val newIp = ip.clauses.map(c => InductiveClause(c.name, c.selector.subst(subst), c.asn.subst(subst).setTagAndRef(rapp)))
      val futures_subst: Subst = if (!rapp.isBorrow) Map.empty
        else if (ip.isPrim || ip.clauses.length == 0) {
          assert(ip.params.length == 1)
          onExpiries.flatMap(_.copyOutSub(rapp.field, ip.params.head._1.subst(subst), !isPre)).toMap
        } else
          ip.params.filter(_._2 != LifetimeType).zipWithIndex.map(p =>
            OnExpiry(Some(!isPre), List(false), rapp.field, p._2, p._1._2).asVar
              -> onExpiryFromParam(p._1._1, ip, predicates).subst(subst)
          ).toMap

      (newIp, args_subst, existentials_subst, fields_subst, futures_subst)
    }
  }

  def loadPrimPred(rapp: RApp, vars: Set[Var], predicates: PredicateEnv, onExpiries: Set[OnExpiry]): (Assertion, Subst) = {
    // There should be no existentials in a primitive pred (so `isPre` is irrelevant)
    val (pred_clauses, _, exists, subst, fut_subst) = loadPred(rapp.copy(ref = rapp.ref match { case Nil => Nil; case r :: _ => List(r) }), vars, predicates, true, onExpiries)
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
      val kont = SubstProducer(newVars.head, field)
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
        (clauses, sbst, fresh_subst, fieldSubst, fut_subst) = loadPred(h, goal.vars, goal.env.predicates, true, goal.onExpiries)
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
          var_name -> (if (field.name == "*" || field.name == "_666") UnaryExpr(OpDeRef, h.field) else BinaryExpr(OpField, h.field, field))
        }.toMap
        val nameSubs = if (h.isBorrow) subs.map(m => m._1 -> UnaryExpr(OpTakeRef(h.ref.head.mut), m._2)) else subs
        val pred = goal.env.predicates(h.pred)
        val kont = MatchProducer(h.field, pred.clean, fieldSubst, nameSubs, pred.clauses.map(c => c.name -> c.asn.sigma.rapps.filter(!_.priv).map(_.field))) >>
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
        val (clauses, sbst, fresh_subst, fieldSubst, fut_subst) = loadPred(h, goal.vars, goal.env.predicates, true, goal.onExpiries)
        if (clauses.length >= 1) {
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
          var_name -> (if (field.name == "*" || field.name == "_666") UnaryExpr(OpDeRef, h.field) else BinaryExpr(OpField, h.field, field))
        }.toMap
        val nameSubs = if (h.isBorrow) subs.map(m => m._1 -> UnaryExpr(OpTakeRef(h.ref.head.mut), m._2)) else subs
        // TODO: Why was the `if (m._2.isInstanceOf[UnaryExpr]) m._2 else ...` here?
        // val nSubsRef = if (h.isBorrow) nameSubs.map(m => m._1 -> (if (m._2.isInstanceOf[UnaryExpr]) m._2 else UnaryExpr(OpTakeRef(h.ref.head.mut), m._2))) else nameSubs
        val pred = goal.env.predicates(h.pred)
        val kont = MatchProducer(h.field, pred.clean, fieldSubst, nameSubs, pred.clauses.map(c => c.name -> c.asn.sigma.rapps.filter(!_.priv).map(_.field))) >>
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
        val call = Call(Var(f.name), f.result, f.params.map(_._1), l)
        val calleePostSigma = f.post.sigma.setSAppTags(PTag(1, 0))
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
        val (clauses, _, fresh_subst, fieldSubst, fut_subst) = loadPred(h, goal.vars, goal.env.predicates, false, goal.onExpiries)
        (InductiveClause(name, selector, asn), idx) <- clauses.zipWithIndex
        if selector != BoolConst(false)
        if asn.sigma.rapps.filter(_.priv).length == (if (clauses.length > 1) 1 else 0)
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
        val construct_args = if (h.isPrim(goal.env.predicates)) h.fnSpec else {
          val fieldNames = goal.env.predicates(h.pred).clauses(idx).asn.sigma.rapps.filter(!_.priv).map(_.field)
          val argNames = asn.sigma.rapps.filter(!_.priv).map(_.field)
          assert(fieldNames.length == argNames.length)
          fieldNames.zip(argNames).map(arg =>
            if (arg._1.name.charAt(0) == '_' && arg._1.name.substring(1).forall(_.isDigit)) arg._2
            else BinaryExpr(OpFieldBind, arg._1, arg._2))
        }
        val kont =
          UnfoldProducer(h.toSApp, selector, Assertion(asn.phi, asn.sigma), fresh_subst ++ fieldSubst) >>
          (if (disc.length == 1) SubstProducer(disc.head.asInstanceOf[RApp].field, disc.head.asInstanceOf[RApp].fnSpec.head) else IdProducer) >>
          AppendProducer(Construct(h.field, goal.env.predicates(h.pred).clean, name, construct_args)) >>
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
        if !goal.existentials.contains(h.field)
        // Cannot expire before reborrowing:
        if !preBorrows.contains(h.field)
        val (clauses, sbst, _, _, fut_subst) = loadPred(h, goal.vars, goal.env.predicates, false, goal.onExpiries)
        InductiveClause(name, selector, asn) <- clauses
        if selector != BoolConst(false)
        // Hacky way to ensure we can only Expire the correct enum variant:
        if selector == BoolConst(true) || {
          val sel = selector.asInstanceOf[BinaryExpr]
          val disc = asn.sigma.rapps.find(d => d.fnSpec.length == 1 && d.fnSpec.head == sel.left).get
          if (goal.pre.sigma.rapps.find(_.field == disc.field).isEmpty)
            println("Goal " + goal.rulesApplied + " could not find disc " + disc.field.pp + " in " + goal.pre.sigma.pp)
          val pre_disc = goal.pre.sigma.rapps.find(_.field == disc.field).get
          if (pre_disc.fnSpec.length != 1) println("Found: " + pre_disc.pp)
          assert(pre_disc.fnSpec.length == 1)
          pre_disc.fnSpec.head.asInstanceOf[Const] == sel.right
        }
      } yield {
        val blocked = asn.sigma.blockRapps(h);
        assert(blocked.borrows.forall(_.blocked == h.blocked));
        val newPost = Assertion(
          // Assumption: selector will be substituted in (since it's an equality when clauses.length != 1)
          goal.post.phi && asn.phi && selector,
          goal.post.sigma ** blocked - h
        )
        RuleResult(List(goal.spawnChild(post = newPost, fut_subst = fut_subst,
            // Hasn't progressed since we didn't progress toward termination, but can be companion
            hasProgressed = false, isCompanionNB = true)), IdProducer, this, goal)
      }
    }
  }
  object ExpireNoWrite extends Expire {
    override def filter(r: RApp, goal: Goal): Boolean = (!goal.isRAppExistential(r, goal.gamma) && (r.ref.length > 1 || goal.env.predicates(r.pred).clauses.length > 1)) || goal.hasPotentialReborrows(r)
  }
  object ExpireFinal extends Expire with InvertibleRule {
    override def filter(r: RApp, goal: Goal): Boolean =
      // Don't need to try writing
      (goal.isRAppExistential(r, goal.gamma) ||
      // Might as well expire if we have no choice; can write to it after expiry if we want to
      // since all the fields will still be there (unlike if we did have an enum)
      (r.ref.length <= 1 && goal.env.predicates(r.pred).clauses.length <= 1)) &&
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
      val reborrowSrcs = goal.post.sigma.borrows.filter(b => !goal.existentials(b.field))
      for {
        src <- reborrowSrcs
        (tgt, subs) <- goal.potentialReborrows(src)
      } yield {
        assert(!tgt.ref.head.beenAddedToPost)
        val tgtPred = goal.env.predicates(tgt.pred)
        assert(tgtPred.params.length == src.fnSpec.length)
        val fut_subst = goal.onExpiries.flatMap(_.reborrowSub(tgt.field, src.field, tgt.fnSpec)).toMap
        // `src.fnSpec` are existentials, need to bind them to all of the futures
        val exists_bind = if (tgt.ref.head.mut)
          src.fnSpec.zipWithIndex.zip(tgtPred.params.map(_._2)).map(p => {
            (OnExpiry(None, true :: List.fill(tgt.ref.length-1)(false), tgt.field, p._1._2, p._2) |===| p._1._1)
          })
        else tgt.fnSpec.zip(src.fnSpec).map(p => (p._1 |===| p._2))
        val newPost = Assertion(
          goal.post.phi && PFormula(exists_bind.toSet).resolveOverloading(goal.gamma),
          (goal.post.sigma - tgt - src) ** src.copy(fnSpec = tgt.fnSpec, blocked = Set())
        )
        // Add lifetime info:
        val newPre = Assertion(
          goal.pre.phi && BinaryExpr(OpOutlived, tgt.ref.head.lft.name, src.ref.head.lft.name),
          goal.pre.sigma
        )
        val kont =
          SubstProducer(tgt.field, src.field) >>
          ExtractHelper(goal)
        RuleResult(List(goal.spawnChild(pre = newPre, post = newPost, fut_subst = fut_subst,
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
        if !goal.isRAppExistential(brrw, goal.gamma) //brrw.isWriteableBorrow(goal.existentials)
      } yield {
        val newOwned = brrw.copy(field = Var(brrw.field.name + "_NV"), ref = brrw.ref.tail, blocked = Set())
        val newBrrw = brrw.refreshFnSpec(goal.gamma, goal.vars).copy(blocked = Set())
        val newPost = Assertion(post.phi, (post.sigma ** newOwned - brrw) ** newBrrw)

        val fut_subst = goal.onExpiries.flatMap(_.writeSub(brrw.field, newOwned.field, newOwned.fnSpec.filter(_.getType(goal.gamma).get != LifetimeType), true)).toMap

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
      
      val lft = newPreBrrw.ref.head.lft
      val lftMax = goal.pre.phi.lftUpperBounds.getOrElse(lft, lft)
      // Only refresh fnspec if mutable
      val newFnSpec =
        if (newPreBrrw.ref.head.mut) newPreBrrw.refreshFnSpec(goal.gamma, goal.vars).fnSpec.map(arg => AlwaysExistsVar(arg.asInstanceOf[Var]))
        else newPreBrrw.fnSpec
      val newPostBrrw = newPreBrrw.copy(
        fnSpec = newFnSpec,
        blocked = goal.pre.phi.outlivesRels.filter(or => or._2 == lftMax).map(_._1)
      )
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
      if (goal.callGoal.isEmpty) return Nil// || goal.callGoal.get.call.companion.isDefined) return Nil
      for {
        src <- goal.pre.sigma.borrows
        // If blocked has either been used as an arg already or was before
        if !src.hasBlocker
        tgt <- goal.post.sigma.borrows
        sub <- src.unify(tgt, true, goal.gamma)
      } yield {
        assert(!goal.existentials(src.field) && goal.existentials(tgt.field))
        // TODO:
        assert(src.fnSpec.forall(_.getType(goal.gamma) != LifetimeType))
        val (newPre, fut_subst) = if (src.ref.head.mut) {
          val blocking = Named(freshVar(goal.vars, src.ref.head.lft.name.name))
          val newSrc = if (tgt.ref.head.mut)
              src.refreshFnSpec(goal.gamma, goal.vars).copy(blocked = Set(blocking))
            else src.copy(blocked = Set(blocking))
          val newPre = Assertion(
            goal.pre.phi && BinaryExpr(OpLftUpperBound, blocking, src.ref.head.lft),
            (goal.pre.sigma - src) ** newSrc
          )
          val fut_subst = if (tgt.ref.head.mut)
              (goal.onExpiries ++ goal.callGoal.get.calleePost.onExpiries).flatMap(_.reborrowCallSub(tgt.field, src.field, src.fnSpec, newSrc.fnSpec, goal.vars)).toMap
            else Map.empty[Var, Expr]
          (newPre, fut_subst + (tgt.ref.head.lft.name -> blocking.name))
        } else {
          (goal.pre, Map(tgt.ref.head.lft.name -> src.ref.head.lft.name))
        }
        // TODO: use?
        // println("\nMade onExpiry: " + src.mkOnExpiry(goal.gamma, Some(false)).pp);
        val phiPost = PFormula(src.fnSpec.zip(tgt.fnSpec).map(args => args._1 |===| args._2).toSet + (src.field |===| tgt.field)).resolveOverloading(goal.gamma)
        val newPost = Assertion(goal.post.phi && phiPost, goal.post.sigma - tgt)
        // println("Calculating fut_subst for: " + goal.rulesApplied)
        // println("Pre: " + goal.pre.pp)
        // println("Post: " + goal.post.pp)
        // println("Calee Post: " + goal.callGoal.get.calleePost.pp)
        RuleResult(List(goal.spawnChild(pre = newPre, post = newPost, fut_subst = fut_subst)), IdProducer, this, goal)
      }
    }
  }

  /*
  KillLft: if no ref has this lft then might as well kill it
   */
  object KillLft extends SynthesisRule with InvertibleRule {

    override def toString: Ident = "KillLft"

    def apply(goal: Goal): Seq[RuleResult] = {
      val usedLfts = goal.pre.sigma.rapps.flatMap(r => r.fnSpec.flatMap(_.collect[Named](_.isInstanceOf[Named])) ++ r.ref.map(_.lft)).toSet
      val tryToKill = goal.pre.sigma.rapps.flatMap(_.blocked)
      val toKill = tryToKill.find(!usedLfts(_))
      if (toKill.isEmpty) Nil
      else {
        val newPre = Assertion(goal.pre.phi, goal.pre.sigma.unblockLft(toKill.get))
        val newGoal = goal.spawnChild(pre = newPre)
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

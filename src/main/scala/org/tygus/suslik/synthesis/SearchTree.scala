package org.tygus.suslik.synthesis

import org.tygus.suslik.language.Statements.Solution
import org.tygus.suslik.logic.Specifications._
import org.tygus.suslik.synthesis.Memoization._
import org.tygus.suslik.synthesis.Termination.Transition
import org.tygus.suslik.synthesis.rules.Rules.{GoalUpdater, RuleResult, SynthesisRule}
import org.tygus.suslik.util.SynStats

import scala.util.DynamicVariable

/**
  * And-or tree that represents the space of all possible derivations
  */
class SearchTree {
  import SearchTree._

  // List of nodes to process
  var worklist: Worklist = List()

  // List of leaf nodes that succeeded
  var successLeaves: Worklist = List()

  // List of nodes to process
  var slns: SolutionList = List()

  // Initialize worklist: root or-node containing the top-level goal
  private def init(initialGoal: Goal): SearchTree = {
    val root = OrNode(Vector(), initialGoal, None)
    worklist = List(root)
    successLeaves = List()
    slns = List()
    this
  }
}

object SearchTree {
  // Rules, Body/Fns, Time
  type SolutionList = List[(Int, Solution, Long)]

  trait SearchNode { val id: NodeId }

  // needs to be thread-local, for `SynthesisServer`
  private val _current = new DynamicVariable[SearchTree](new SearchTree)
  def st: SearchTree = _current.value

  // need to gradually get rid of those in favor of instance methods on `st`
  def worklist: Worklist = st.worklist
  def worklist_=(w: Worklist): Unit = { st.worklist = w }
  def successLeaves: Worklist = st.successLeaves
  def successLeaves_=(w: Worklist): Unit = { st.successLeaves = w }
  def slns: SolutionList = st.slns
  def slns_=(w: SolutionList): Unit = { st.slns = w }

  /**
    * Node's position in the search tree
    * (index of each reflexive ancestor among its siblings; youngest to oldest)
    */
  type NodeId = Vector[Int]

  type Worklist = List[OrNode]

  def init(initialGoal: Goal): Unit = {
    _current.value = new SearchTree().init(initialGoal)
  }

  /**
    * Or-node in the search tree;
    * represents a synthesis goal to solve.
    * For this node to succeed, one of its children has to succeed.
    */
  case class OrNode(id: NodeId, goal: Goal, parent: Option[AndNode], extraCost: Int = 0) extends SearchNode {
    var parentSucceeded: Boolean = false
    // My index among the children of parent
    def childIndex: Int = id.headOption.getOrElse(0).max(0)

    // Does this node have a ancestor with label l?
    def hasAncestor(l: Vector[Int]): Boolean =
      if (id == l) true
      else if (id.length < l.length) false
      else parent match {
        // this node cannot be the root, because label.lengh > l.length
        case Some(p) => p.hasAncestor(l)
        case _ => false
      }

    // This node has failed: prune siblings from worklist
    def fail(implicit stats: SynStats, config: SynConfig): Unit = {
      if (memo.lookup(goal).map(_.isInstanceOf[Succeeded]).getOrElse(false)) return
      memo.save(goal, Failed)
      parent match {
        case None => assert(st.worklist.isEmpty)// this is the root; wl must already be empty
        case Some(an) => { // a subgoal has failed
          stats.addFailedNode(an)
          st.worklist = pruneDescendants(an.id, st.worklist)  // prune all other descendants of an
          st.successLeaves = pruneDescendants(an.id, st.successLeaves) // also from the list of succeeded leaves
          if (!st.worklist.exists(_.hasAncestor(an.parent.id))) { // does my grandparent have other open alternatives?
            an.parent.fail
          }
        }
      }
    }

    // This node has succeeded: return either its next suspended and-sibling or the solution
    def succeed(s: List[(Int, Solution)])(implicit config: SynConfig): Either[Option[OrNode], List[(Int, Solution)]] = {
      memo.save(goal, Succeeded(s, id))
      succeedDescendants(id, st.worklist) // succeed all my descendants in worklist
      st.successLeaves = st.successLeaves.filterNot(n => this.isFailedDescendant(n))  // prune members of partially successful branches
      parent match {
        case None => Right(s) // this is the root: synthesis succeeded
        case Some(an) => { // a subgoal has succeeded
          val idx = if (an.nChildren == 1) 0 else this.id.head
          if (idx >= an.childSolutions.length) {
            println("Have env " + an.nChildren + " with id " + this.id)
            println("childSolutions " + an.childSolutions.length)
          }
          an.childSolutions = an.childSolutions.updated(idx, s ++ an.childSolutions(idx))
          // Check if my parent has more open subgoals:
          if (an.nextChildIndex == an.nChildren) { // there are no more open subgoals: an has succeeded
            def generator2(x: List[List[(Int, Solution)]]): List[List[(Int, Solution)]] = x match {
              case Nil    => List(Nil)
              case h :: t => for (j <- generator2(t); i <- h) yield i :: j
            }
            val sols = generator2(an.childSolutions.updated(idx, s)).map(sln => (sln.map(_._1).sum + 1, an.kont(sln.map(_._2)))) // compute solution
            if (sols.length == 0) Left(None)
            else an.parent.succeed(sols) // tell parent it succeeded
          } else { // there are other open subgoals: add next open subgoal to the worklist
            Left(Some(an.nextChild))
          }
        }
      }
    }

    // Worklist `wl` with all descendants of `ancestor` pruned
    private def pruneDescendants(ancestor: NodeId, wl: List[OrNode]): List[OrNode] = {
      val (toForget, newWL) = wl.partition(_.hasAncestor(ancestor))
      toForget.foreach(_.forget(ancestor))
      newWL
    }

    // Worklist `wl` with all descendants of `ancestor` succeeded
    private def succeedDescendants(ancestor: NodeId, wl: List[OrNode]) = {
      wl.filter(_.hasAncestor(ancestor)).foreach(_.parentSucceeded = true)
    }

    // Remove reflexive ancestors of this node until `until` from memo
    private def forget(until: NodeId): Unit = parent match {
      case None =>
      case Some(an) => if (an.id.length >= until.length) {
        memo.forgetExpanded(this.goal)
        an.parent.forget(until)
      }
    }

    // Is n part of a branch of my descendants that hasn't yet fully succeeded?
    // Yes if there's a incomplete and-node on the way from n to me
    private def isFailedDescendant(n: OrNode): Boolean =
      n.andAncestors.find(an => an.childSolutions.length < an.nChildren) match {
      case None => false
      case Some(an) => an.hasAncestor(this.id)
    }

    // And nodes that are proper ancestors of this node in the search tree
    def andAncestors: List[AndNode] = parent match {
      case None => Nil
      case Some(p) => p :: p.parent.andAncestors
    }

    // Or-nodes that are proper ancestors of this node in the search tree
    def ancestors: List[OrNode] = andAncestors.map(_.parent)

    // Rules that lead to this node
    def ruleHistory: List[SynthesisRule] = andAncestors.map(_.rule)

    // Number of proper ancestors
    def depth: Int = ancestors.length

    // Is other from the same branch of the search as myself?
    private def isAndSibling(other: OrNode): Boolean = {
      val leastCommonAndAncestor = andAncestors.find(an => other.andAncestors.contains(an))
      leastCommonAndAncestor match {
        case None => false // this can happen if the only common ancestor is root
        case Some(lcan) => {
          val lcon = ancestors.find(on => other.ancestors.contains(on)).get
          // Since these are least common ancestors, one must be the parent of the other
          assert(lcon.parent.contains(lcan) || lcan.parent == lcon)
          // we are and-siblings if our least common and-ancestor is below our least common or-ancestor:
          lcan.parent == lcon
        }
      }
    }

    // The partial derivation that this node is part of (represented as a subset of success leaves)
    def partialDerivation: List[OrNode] = st.successLeaves.filter(isAndSibling)

    def pp(d: Int = 0): String = parent match {
      case None => "-"
      case Some(p) =>
        if (d > 2) s"...($depth)"
        else {
          val subgoalID = if (id.head < 0) "" else s".${id.head}"
          p.pp(d + 1) ++ subgoalID
        }
    }

    lazy val cost: Int = {
      goal.cost.max(extraCost)
    }

    override def equals(obj: Any): Boolean = obj.isInstanceOf[OrNode] && (obj.asInstanceOf[OrNode].id == this.id)
    override def hashCode(): Int = id.hashCode()
  }

  /**
    * And-node in the search tree;
    * represents a set of premises of a rule application, whose result should be combined with kont.
    * For this node to succeed, all of its children (premises, subgoals) have to succeed.
    */
  class AndNode(_id: NodeId, _parent: OrNode, _result: RuleResult) extends SearchNode {
    val id: NodeId = _id                                      // Unique id within the search tree
    val parent: OrNode = _parent                              // Parent or-node
    val rule: SynthesisRule = _result.rule                    // Rule that was applied to create this node from parent
    val childGoals: Seq[Goal] = _result.subgoals              // Goals of all child or-nodes
    val transitions: Seq[Transition] = _result.transitions    // Transitions between goals added during rule application (for termination checking)
    val kont: StmtProducer = _result.producer                 // Statement producer: combines solutions from children into a single solution
    val updates: Seq[GoalUpdater] = _result.updates           // How to update goals of future children based on solutions of succeeded children
    var nextChildIndex: Int = 0                               // The index of first child that hasn't yet been explored
    var childSolutions: List[List[(Int, Solution)]] =         // Solutions of children that already succeeded
      (1 to nChildren).map(_ => List.empty).toList

    // Does this node have an ancestor with label l?
    def hasAncestor(l: NodeId): Boolean =
      if (id == l) true
      else if (id.length < l.length) false
      else parent.hasAncestor(l)

    // Total number of child or nodes
    def nChildren: Int = childGoals.size

    // Return the first previously suspended or-node and increase nextChildIndex
    def nextChild: OrNode = {
      val origGoal = childGoals(nextChildIndex)
      val goal = updates(nextChildIndex)(childSolutions.flatMap(_.headOption.map(_._2)))(origGoal)
      val j = if (nChildren == 1) -1 else nextChildIndex
      val extraCost = (0 +: childGoals.drop(nextChildIndex + 1).map(_.cost)).max
      nextChildIndex = nextChildIndex + 1
      OrNode(j +: this.id, goal, Some(this), parent.extraCost.max(extraCost))
    }

    def pp(d: Int = 0): String = {
      val parentPP = parent.parent match {
        case None => ""
        case Some(_) => s"${parent.pp(d)}-"
      }
      parentPP ++ rule.toString
    }

    override def equals(obj: Any): Boolean = obj.isInstanceOf[AndNode] && (obj.asInstanceOf[AndNode].id == this.id)
    override def hashCode(): Int = id.hashCode()
  }

  object AndNode {
    def apply(id: NodeId, parent: OrNode, result: RuleResult): AndNode =
      new AndNode(id, parent, result)
  }

}

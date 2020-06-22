package org.tygus.suslik.certification

import org.tygus.suslik.logic.Specifications.{Footprint, Goal}
import org.tygus.suslik.synthesis.SearchTree.{AndNode, NodeId, OrNode}
import org.tygus.suslik.synthesis.{StmtProducer, SynthesisException}
import org.tygus.suslik.synthesis.rules.Rules.{RuleResult, SynthesisRule}

import scala.collection.mutable

object CertTree {
  private var counter: Int = 0
  /**
    * [Certify]: A utility for traversing a successful synthesis result during certification
    * @param id the NodeId of the associated or-node in the synthesis search tree
    * @param goal the current synthesis goal
    * @param kont the continuation that produces the statement for the goal
    * @param rule the synthesis rule that was successfully applied to prove the goal
    * @param produce the `produce` footprint of the associated or-node
    * @param consume the `consume` footprint of the associated and-node
    */
  case class Node(id: NodeId,
                  goal: Goal,
                  kont: StmtProducer,
                  rule: SynthesisRule,
                  produce: Footprint,
                  consume: Footprint) {
    val cid: Int = { val n = counter; counter += 1; n }
    def children: List[Node] = childrenMap.getOrElse(this, List.empty).reverse
    def parent: Option[Node] = parentMap.get(this)

    override def equals(obj: Any): Boolean = obj.isInstanceOf[Node] && (obj.asInstanceOf[Node].id == this.id)
    override def hashCode(): Int = id.hashCode()


    private def showFootprint(f: Footprint): String = s"{${f.pre.pp}}{${f.post.pp}}"

    def pp: String = {
      val cs = children

      val builder = new StringBuilder()
      builder.append(s"Node <${hashCode()}>\n")

      builder.append(s"Goal to solve:\n")

      builder.append(s"${goal.pp}\n")

      builder.append(s"Rule applied: $rule\n")

      val childProds = if (cs.nonEmpty) cs.map(c => showFootprint(c.produce)).mkString(", ") else "nothing"
      builder.append(s"Footprint: ${showFootprint(consume)} --> $childProds\n")

      builder.append(s"Parent node: ${parent.map(_.hashCode()).getOrElse("none")}\n")
      builder.append(s"Child nodes: [${cs.map(_.hashCode()).mkString(", ")}]\n")

      builder.toString()
    }
  }

  // [Certify]: Maintain a certification tree as a pair of bidirectional hash maps
  private val childrenMap: mutable.Map[Node, List[Node]] = mutable.Map.empty
  private val parentMap: mutable.Map[Node, Node] = mutable.Map.empty
  def root: Option[Node] = get(Vector())

  /**
    * [Certify]: Adds a successful terminal or-node and its ancestors
    * from the synthesis search tree to this certification tree
    * @param terminal a terminal or-node in the search tree
    * @param e a successful rule expansion for the terminal or-node
    */
  def addSuccessfulPath(terminal: OrNode, e: RuleResult): Unit = {
    def mkKont(n: Node, prevKont: Node => Unit): Node => Unit = parent => {
      prevKont(n)  // execute the rest of the continuation
      parentMap(n) = parent  // add link: child -> parent
      childrenMap(parent) =  // add link: parent -> child
        n :: childrenMap.getOrElse(parent, List.empty)
    }

    @scala.annotation.tailrec
    def traverse(an: AndNode, kont: Node => Unit): Unit = {
      val on = an.parent
      val n = Node(on.id, on.goal, an.kont, an.rule, on.produce, an.consume)
      on.parent match {
        case Some(parentAn) if !parentMap.contains(n) =>  // only continue if parent hasn't been added before
          traverse(parentAn, mkKont(n, kont))
        case _ =>
          kont(n)
      }
    }

    val terminalAn = AndNode(Vector(), e.producer, terminal, e.consume, e.rule)
    traverse(terminalAn, _ => ())
  }

  def get(id: NodeId): Option[Node] = childrenMap.keySet.find(_ == Node(id, null, null, null, null, null))

  def clear(): Unit = {
    childrenMap.clear
    parentMap.clear
  }

  // Pretty prints the tree rooted at a node (tries the root node by default)
  def pp(id: NodeId = Vector()): String = {
    def visit(n: Node): String = {
      val builder = new StringBuilder()
      builder.append(n.pp)
      builder.append("\n")
      for (child <- n.children)
        builder.append(visit(child))
      builder.toString()
    }

    val n = get(id).getOrElse(throw SynthesisException(s"No node found matching id $id"))
    visit(n)
  }
}

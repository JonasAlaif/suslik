package org.tygus.suslik

import org.tygus.suslik.language._
import org.tygus.suslik.language.Expressions._

package object logic {

  type Formals = List[(Var, SSLType)]
  type PredicateEnv = Map[Ident, InductivePredicate]
  type PredicateCycles = Set[Ident]
  type FunctionEnv = Map[Ident, FunSpec]
  type Gamma =  Map[Var, SSLType]
}

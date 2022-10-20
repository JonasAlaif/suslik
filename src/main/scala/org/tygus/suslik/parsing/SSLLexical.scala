package org.tygus.suslik.parsing

import scala.util.parsing.combinator.lexical.StdLexical

/**
  * @author Ilya Sergey
  */
class SSLLexical extends StdLexical {

  // Add keywords
  reserved += ("if", "then", "else", "true", "false", "emp", "not", "return", "predicate", "in", "lower", "upper")
  reserved += ("unreachable","magic","malloc", "free", "let", "assume")
  reserved += ("null")
  reserved += ("mut", "priv")

  // Types
  reserved += ("int", "lft", "bool", "loc", "set", "interval")

  delimiters += ("(", ")", "=", ";", "**", "*", ":->", "=i", "<=i", "++", "--", "..",
      "{", "}", "/\\", "&&", "\\/", "||", "\n", "\r", "=>", "?", ":", "&", "^", "#",
      "<", ">", ",", "/", "+", "-", "==", "!=", "==>", "<=", ">=", "[", "]", "|", "??"
  )

}

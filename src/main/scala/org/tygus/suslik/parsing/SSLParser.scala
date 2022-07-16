package org.tygus.suslik.parsing

import org.tygus.suslik.language.Expressions._
import org.tygus.suslik.language.Statements._
import org.tygus.suslik.language._
import org.tygus.suslik.logic.Specifications._
import org.tygus.suslik.logic._
import org.tygus.suslik.synthesis._
import org.tygus.suslik.LanguageUtils._

import scala.annotation.tailrec
import scala.collection.mutable.ListBuffer
import scala.util.parsing.combinator.syntactical.StandardTokenParsers

class SSLParser(config: SynConfig = defaultConfig) extends StandardTokenParsers with SepLogicUtils {

  // Modified repN
  def repAll[T](p: => Parser[T]): Parser[List[T]] =
    Parser { in =>
      val elems = new ListBuffer[T]
      val p0 = p // avoid repeatedly re-evaluating by-name parser

      @tailrec def applyp(in0: Input): ParseResult[List[T]] =
        if (in0.atEnd) Success(elems.toList, in0)
        else p0(in0) match {
          case Success(x, rest) => elems += x; applyp(rest)
          case ns: NoSuccess => ns
        }

      applyp(in)
    }

  override val lexical = new SSLLexical

  def typeParser: Parser[SSLType] =
    ("int" ^^^ IntType
      | "lft" ^^^ LifetimeType
      | "bool" ^^^ BoolType
      | "loc" ^^^ LocType
      | "set" ^^^ IntSetType
      | "interval" ^^^ IntervalType
      | "void" ^^^ VoidType)

  def formal: Parser[(Var, SSLType)] = typeParser ~ varParser ^^ { case a ~ b => (b, a) }

  def locLiteral: Parser[Const] =
    "null" ^^ (_ => NilPtr)

  def intLiteral: Parser[IntConst] =
    numericLit ^^ (x => IntConst(Integer.parseInt(x)))

  def boolLiteral: Parser[BoolConst] =
    ("true" | "false") ^^ (b => BoolConst(java.lang.Boolean.parseBoolean(b)))

  def setLiteral: Parser[Expr] =
    "{" ~> repsep(expr, ",") <~ "}" ^^ SetLiteral

  def intervalLiteral: Parser[Expr] = {
    def intervalInternal: Parser[Expr] = opt(expr ~ opt(".." ~> expr)) ^^ {
      case None => emptyInt
      case Some(e ~ None) => BinaryExpr(OpRange, e, e)
      case Some(e1 ~ Some(e2)) => BinaryExpr(OpRange, e1, e2)
    }
    "[" ~> intervalInternal <~ "]"
  }

  def varParser: Parser[Var] = "&" ~> ident ^^ { v => Var(v + "-L") } ||| ident ^^ Var

  def unOpParser: Parser[UnOp] =
    ("not" ^^^ OpNot ||| "-" ^^^ OpUnaryMinus ||| "lower" ^^^ OpLower ||| "upper" ^^^ OpUpper)

  // TODO: remove legacy ++, --, =i, /\, \/, <=i
  def termOpParser: Parser[OverloadedBinOp] = "*" ^^^ OpOverloadedStar

  // TODO: remove legacy ++, --, =i, /\, \/, <=i
  def addOpParser: Parser[OverloadedBinOp] = (
    ("++" ||| "+") ^^^ OpOverloadedPlus
      ||| ("--" ||| "-") ^^^ OpOverloadedMinus
    )

  def relOpParser: Parser[OverloadedBinOp] = (
    "<" ^^^ OpLt
      ||| ">" ^^^ OpGt
      ||| ">=" ^^^ OpGeq
      ||| "!=" ^^^ OpNotEqual
      ||| ("==" | "=i") ^^^ OpOverloadedEq
      ||| ("<=" ||| "<=i") ^^^ OpOverloadedLeq
      ||| "in" ^^^ OpOverloadedIn
    )

  def logOpParser: Parser[OverloadedBinOp] = (
    ("\\/" | "||") ^^^ OpOr
      ||| ("/\\" | "&&") ^^^ OpAnd
      ||| "==>" ^^^ OpImplication
    )

  def binOpParser(p: Parser[OverloadedBinOp]): Parser[(Expr, Expr) => Expr] = {
    p ^^ { op => (l, r) => OverloadedBinaryExpr(op, l, r) }
  }

  def atom: Parser[Expr] = (
    unOpParser ~ atom ^^ { case op ~ a => UnaryExpr(op, a) }
      | "(" ~> repsep(expr, ",") <~ ")" ^^ { case e::Nil => e; case es => TupleExpr(es.map((_, None))) }
      | intLiteral | boolLiteral | setLiteral | locLiteral | intervalLiteral
      | varParser | noExists | onExpiry
    )

  def term: Parser[Expr] = chainl1(atom, binOpParser(termOpParser))

  def addExpr: Parser[Expr] = chainl1(term, binOpParser(addOpParser))

  def relExpr: Parser[Expr] =
    addExpr ~ opt(relOpParser ~ addExpr) ^^ {
      case a ~ None => a
      case a ~ Some(op ~ b) => OverloadedBinaryExpr(op, a, b)
    }

  def expr: Parser[Expr] =
    chainl1(relExpr, binOpParser(logOpParser)) ~ opt(("?" ~> expr <~ ":") ~ expr) ^^ {
      case a ~ None => a
      case a ~ Some(l ~ r) => IfThenElse(a, l, r)
    }

  def noExists: Parser[NoExists] = "#" ~> "[" ~> expr <~ "]" ^^ { case e => NoExists(e) }
  def onExpiry: Parser[OnExpiry] = rep1("^" ^^^ true | "*" ^^^ false) ~ ("(" ~> typeParser ~ varParser <~ ")") ~ ("[" ~> numericLit <~ "]") ^^ { case futs ~ (ty ~ f) ~ i => OnExpiry(None, futs.reverse, f, Integer.parseInt(i), ty) }

  def lft: Parser[Named] = ident ^^ (l => Named(Var(l + "-L")))

  def ref: Parser[Ref] =
    ("&" ~> lft) ~ opt("mut") ^^ { case l ~ mut => Ref(l, mut.isDefined, false) }

  def identWithOffset: Parser[(Ident, Int)] = {
    val ov = ident ~ opt("+" ~> numericLit)
    ("(" ~> ov <~ ")" | ov) ^^ { case i ~ o =>
      val off = Math.max(Integer.parseInt(o.getOrElse("0")), 0)
      (i, off)
    }
  }

  private def defaultCardParameter: Expr = if (config.simple) IntConst(0)
                                           else Var(getTotallyFreshName(cardinalityPrefix))

  def heaplet: Parser[Heaplet] = (
    (identWithOffset <~ ":->") ~ expr ^^ { case (a, o) ~ b => PointsTo(Var(a), o, b) }
      ||| "[" ~> (ident ~ ("," ~> numericLit)) <~ "]" ^^ { case a ~ s => Block(Var(a), Integer.parseInt(s)) }
      ||| ident ~ ("(" ~> rep1sep(expr, ",") <~ ")") ~ opt("<" ~> expr <~ ">") ^^ {
        case name ~ args ~ v => SApp(name, args, PTag(), v.getOrElse(defaultCardParameter))
      }
      ||| opt("priv") ~ (varParser <~ ":") ~ rep(ref) ~ ident ~ ("(" ~> repsep(expr, ",") <~ ")") ~ opt("<" ~> rep1sep(lft, "+") <~ ">") ^^ {
        case priv ~ field ~ r ~ pred ~ fnSpec ~ None => RApp(priv.isDefined, field, r, pred, fnSpec, Set(), PTag())
        case priv ~ field ~ r ~ pred ~ fnSpec ~ Some(b) => RApp(priv.isDefined, field, r, pred, fnSpec, b.toSet, PTag())
      }
    )

  def sigma: Parser[SFormula] = (
    "emp" ^^^ emp
      ||| repsep(heaplet, "**") ^^ { hs => mkSFormula(hs) }
    )

  def assertion: Parser[Assertion] = "{" ~> (opt(expr <~ ";") ~ sigma) <~ "}" ^^ {
    case Some(p) ~ s => Assertion(toFormula(desugar(p)), s)
    case None ~ s => Assertion(pTrue, s)
  }

  def indClause: Parser[InductiveClause] =
    expr ~ ("=>" ~> opt(ident) ~ assertion) ^^ { case p ~ (n ~ a) => InductiveClause(n, desugar(p), a) }

  def indPredicate: Parser[InductivePredicate] =
    opt("priv") ~ ("predicate" ~> ident) ~ ("(" ~> repsep(formal, ",") <~ ")") ~
      opt("[" ~> ident <~ "]") ~ opt(ident) ~
      (("{" ~ opt("|")) ~> repsep(indClause, "|") <~ "}") ^^ {
      case priv ~ name ~ formals ~ card ~ cleanName ~ clauses =>
        InductivePredicate(priv.isDefined, name, formals, clauses, cleanName.map(_.substring(1)))
    }

  type UGoal = (Assertion, Set[Var])

  def uGoal: Parser[UGoal] = ("(" ~> rep1sep(varParser, ",") <~ ")") ~ assertion ^^ {
    case params ~ formula => (formula, params.toSet)
  }

  def varsDeclaration: Parser[Formals] = "[" ~> repsep(formal, ",") <~ "]"

  def goalFunctionSYN: Parser[FunSpec] = assertion ~ typeParser ~ ident ~ ("(" ~> repsep(formal, ",") <~ ")") ~ varsDeclaration.? ~ assertion ^^ {
    case pre ~ tpe ~ name ~ formals ~ vars_decl ~ post => FunSpec(name, tpe, formals, pre, post,  vars_decl.getOrElse(Nil))
  }

  def nonGoalFunction: Parser[FunSpec] = typeParser ~ ident ~ ("(" ~> repsep(formal, ",") <~ ")") ~ varsDeclaration.? ~ assertion ~ assertion ^^ {
    case tpe ~ name ~ formals ~ vars_decl ~ pre ~ post => FunSpec(name, tpe, formals, pre, post, vars_decl.getOrElse(Nil))
  }

  def statementParser: Parser[Statement] = (
    ("??" ^^^ Hole)
      ||| ("error" ~> ";" ^^^ Statements.Error)
      // Malloc
      ||| "let" ~> varParser ~ ("=" ~> "malloc" ~> "(" ~> numericLit <~ ")" ~> ";") ^^ {
      case variable ~ number_str => Malloc(variable, IntType, Integer.parseInt(number_str)) // todo: maybe not ignore type here
    }
      ||| ("free" ~> "(" ~> varParser <~ ")" ~> ";") ^^ Free
      // Store
      ||| "*" ~> varParser ~ ("=" ~> expr <~ ";") ^^ {
      case variable ~ e => Store(variable, 0, desugar(e))
    }
      ||| ("*" ~> "(" ~> varParser <~ "+") ~ numericLit ~ (")" ~> "=" ~> expr <~ ";") ^^ {
      case variable ~ offset_str ~ e => Store(variable, Integer.parseInt(offset_str), desugar(e))
    }
      // Load
      ||| ("let" ~> varParser) ~ ("=" ~> "*" ~> varParser <~ ";") ^^ {
      case to ~ from => Load(to, IntType, from) // todo: maybe not ignore type here
    }
      ||| ("let" ~> varParser <~ "=" <~ "*" <~ "(") ~ (varParser <~ "+") ~ (numericLit <~ ")" <~ ";") ^^ {
      case to ~ from ~ offset_str => Load(to, IntType, from, Integer.parseInt(offset_str)) // todo: maybe not ignore type here
    }
      // Call
      ||| opt("let" ~> ("(" ~> repsep(varParser, ",") <~ ")") <~ "=") ~ varParser ~ ("(" ~> repsep(expr, ",") <~ ")" <~ ";") ^^ {
      case result ~ fun ~ args => Call(fun, result.getOrElse(List.empty), args.map(desugar), None)
    }
      // if
      ||| ("if" ~> "(" ~> expr <~ ")") ~ ("{" ~> codeWithHoles <~ "}") ~ ("else" ~> "{" ~> codeWithHoles <~ "}") ^^ {
      case cond ~ tb ~ eb => If(desugar(cond), tb, eb)
    }
    // Guarded
    //      ||| ("assume" ~> "(" ~> expr <~ ")") ~ ("{" ~> codeWithHoles <~ "}")  ^^ {
    //        case cond ~ body => Guarded(desugar(cond), body)
    //      }
    )

  def codeWithHoles: Parser[Statement] = rep(statementParser) ^^ (seq => if (seq.nonEmpty) seq.reduceRight(SeqComp) else Skip)


  def goalFunctionV1: Parser[GoalContainer] = nonGoalFunction ~ ("{" ~> codeWithHoles <~ "}") ^^ {
    case goal ~ body => GoalContainer(goal, body)
  }

  def programSUS: Parser[Program] = phrase(rep(indPredicate | (goalFunctionV1 ||| nonGoalFunction))) ^^ { pfs =>
    val ps = for (p@InductivePredicate(_, _, _, _, _) <- pfs) yield p
    val fs = for (f@FunSpec(_, _, _, _, _, _) <- pfs) yield f
    val goals = for (gc@GoalContainer(_, _) <- pfs) yield gc
    if (goals.isEmpty) {
      throw SynthesisException("Parsing failed: no single goal spec is provided.")
    }
    if (goals.size > 1) {
      throw SynthesisException("Parsing failed: more than one goal is provided.")
    }
    val goal = goals.last
    Program(ps, fs, goal)
  }

  def programSYN: Parser[Program] = phrase(rep(indPredicate | goalFunctionSYN)) ^^ { pfs =>
    val ps = for (p@InductivePredicate(_, _, _, _, _) <- pfs) yield p
    val fs = for (f@FunSpec(_, _, _, _, _, _) <- pfs) yield f
    if (fs.isEmpty) {
      throw SynthesisException("Parsing failed. No single function spec is provided.")
    }
    val goal = fs.last
    val funs = fs.take(fs.length - 1)
    Program(ps, funs, GoalContainer(goal, Hole))
  }

  def parse[T](p: Parser[T])(input: String): ParseResult[T] = p(new lexical.Scanner(input)) match {
    case e: Error => Failure(e.msg, e.next)
    case s => s
  }

  def parseUnificationGoal(input: String): ParseResult[UGoal] = parse(uGoal)(input)

  def parseGoalSYN(input: String): ParseResult[Program] = parse(programSYN)(input)

  def parseGoalSUS(input: String): ParseResult[Program] = parse(programSUS)(input)

  def parseGoal = parseGoalSYN _
}

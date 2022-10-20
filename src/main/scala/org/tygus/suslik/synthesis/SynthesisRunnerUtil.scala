package org.tygus.suslik.synthesis

import java.io.{File, PrintWriter}
import java.nio.file.Paths

import org.tygus.suslik.LanguageUtils
import org.tygus.suslik.certification.CertificationTarget.NoCert
import org.tygus.suslik.certification.source.SuslikProofStep
import org.tygus.suslik.certification.CertTree
import org.tygus.suslik.language.Statements
import org.tygus.suslik.logic.Environment
import org.tygus.suslik.logic.Preprocessor._
import org.tygus.suslik.logic.smt.SMTSolving
import org.tygus.suslik.parsing.SSLParser
import org.tygus.suslik.report.{Log, ProofTrace, ProofTraceJsonFile, ProofTraceCert, ProofTraceJson, ProofTraceNone, StopWatch}
import org.tygus.suslik.synthesis.SearchTree.AndNode
import org.tygus.suslik.synthesis.tactics._
import org.tygus.suslik.util._
import resource.managed

import scala.io.Source

/**
  * @author Nadia Polikarpova, Ilya Sergey
  */

trait SynthesisRunnerUtil {

  {
    // Warm up SMT solver:
    SMTSolving
  }

  val log : Log = new Log(SynLogLevels.Test)

  val testSeparator = "###"
  val testExtension = "syn"
  val sketchExtension = "sus"
  val defExtension = "def"
  val paramPrefix = "#"
  val noOutputCheck = "nope"

  // The path starts from the project root.
  val rootDir: String = "./src/test/resources/synthesis".replace("/", File.separator)

  def doRun(testName: String, desc: String, in: String, out: String, params: SynConfig = defaultConfig) = {
    LanguageUtils.resetFreshNameGenerator()
  }

  def getDescInputOutput(testFilePath: String, initialParams: SynConfig = defaultConfig): (String, String, String, String, SynConfig) = {
    val file = new File(testFilePath)
    val format = testFilePath match {
      case s if s.endsWith(testExtension) => dotSyn
      case s if s.endsWith(sketchExtension) => dotSus
    }
    // The path is counted from the root
    val allLines = readLines(file)
    val (params, lines) =
      if (allLines.nonEmpty && allLines.head.startsWith(paramPrefix)) {
        (SynthesisRunner.parseParams(allLines.head.drop(paramPrefix.length).split(' '), initialParams), allLines.tail)
      } else (initialParams, allLines)

    def splitAtSeparator(lines: List[String], default: List[String] = List()): (List[String], List[String]) = {
      val i = lines.indexWhere(_.trim.contains(testSeparator))
      if (i == -1) (lines, default)
      else {
        val (before, _ :: after) = lines.splitAt(i) // a::b matches head `a` and tail `b`
        (before, after)
      }
    }

    def parseSyn = {
      val (testDescr, afterDescr) = splitAtSeparator(lines)
      val fname = removeSuffix(file.getName, s".$testExtension")
      val dirName = file.getParentFile.getName
      val description = if (testDescr.isEmpty) "Testing synthesis" else testDescr.mkString("\n").trim
      // The first part is the description
      val testName = s"$dirName/$fname"
      val desc = s"[$testName] $description"

      val (spec, afterSpec) = splitAtSeparator(afterDescr)
      val input = spec.mkString(" ").trim

      val (expectedSrc, rawScript) = splitAtSeparator(afterSpec)
      val output = expectedSrc.mkString("\n").trim
      val script = rawScript.mkString("\n").trim.split("\n").toList.filter(_.nonEmpty).map(_.toInt)
      (testName, desc, input, output, params.copy(inputFormat = format, script = script))
    }

    def parseSus = {
      val hasDescr = lines.head.trim.startsWith("/*")
      val desc = if(hasDescr) lines.head.trim else ""

      val (spec, expectedSrc) = splitAtSeparator(lines, List(noOutputCheck))

      val input = spec.mkString("\n").trim
      val testName = testFilePath
      val output = expectedSrc.mkString("\n").trim
      (testName, desc, input, output, params.copy(inputFormat = format))
    }

    format match {
      case `dotSyn` => parseSyn
      case `dotSus` => parseSus
    }
  }

  def prepareSynthesisTask(text: String, params: SynConfig = defaultConfig) = {
    val parser = new SSLParser(params)
    val res = params.inputFormat match {
      case `dotSyn` => parser.parseGoalSYN(text)
      case `dotSus` => parser.parseGoalSUS(text)
    }
    if (!res.successful) {
      throw SynthesisException(s"Failed to parse the input:\n$res")
    }

    val prog = res.get
    val (specs, predEnv, predCycles, funcEnv, body) = preprocessProgram(prog, params)

    if (specs.lengthCompare(1) != 0) {
      throw SynthesisException("Expected a single synthesis goal")
    }

    val spec = specs.head
    val env = Environment(predEnv, predCycles, funcEnv, params, new SynStats(params.timeOut))
    (spec, env, body)
  }

  // Create synthesizer object, choosing search tactic based on the config
  def createSynthesizer(env: Environment): Synthesis = {
    val tactic =
      if (env.config.interactive) {
        if (env.config.simple)
          new InteractiveSimple(env.config, env.stats)
        else
          new InteractiveRust(env.config, env.stats)
      } else if (env.config.script.nonEmpty)
        new ReplaySynthesis(env.config)
      else if (env.config.simple)
        new AutomaticSimple(env.config)
      else
        new AutomaticRust(env.config)
    val trace : ProofTrace = if (env.config.certTarget != NoCert) new ProofTraceCert() else {
      env.config.traceToJsonFile match {
        case None => ProofTraceNone
        case Some(file) => new ProofTraceJsonFile(file)
      }
    }
    new Synthesis(tactic, log, trace)
  }

  def synthesizeFromFile(dir: String, testName: String,
                         initialParams: SynConfig = defaultConfig) : List[List[Statements.Procedure]] = {
    val fullPath = Paths.get(dir, testName)
    val defs = getDefsFromDir(new File(dir))
    val (_, _, in, out, params) = getDescInputOutput(fullPath.toString, initialParams)
    synthesizeFromSpec(testName, List(defs, in).mkString("\n"), out, params)
  }

  def synthesizeFromSpec(testName: String, text: String, out: String = noOutputCheck,
                         params: SynConfig = defaultConfig) : List[List[Statements.Procedure]] = {
    import log.out.testPrintln

    val (spec, env, body) = prepareSynthesisTask(text, params)
    val synthesizer = createSynthesizer(env)

    env.stats.start()
    val sresult = synthesizer.synthesizeProc(spec, env, body)
    val duration = env.stats.duration

    SynStatUtil.log(testName, duration, params, spec, sresult._1, sresult._2)

    def printRuleApplication(name: String, stat: RuleStat): String =
      s"$name: succeeded ${stat.numSuccess} times (${stat.timeSuccess}ms), failed ${stat.numFail} times (${stat.timeFail}ms)"

    def printStats(stats: SynStats) = {
      testPrintln(s"Goals generated: ${stats.numGoalsGenerated}")
      testPrintln(s"Goals expanded: ${stats.numGoalsExpanded}")
      testPrintln(s"And-nodes backtracked: ${stats.numGoalsFailed}")
      testPrintln(s"Maximum worklist size: ${stats.maxWorklistSize}")
      testPrintln(s"Maximum goal depth: ${stats.maxGoalDepth}")
      testPrintln(s"Final memo size: ${stats.memoSize}")
      testPrintln(s"Final size of SMT cache: ${stats.smtCacheSize}")
      testPrintln(s"Time spent cycling: ${stats.timeCycling}ms")
//      val hotNodesString = stats.hotNodes(5).map{case (n, s) => printHotNode(n, s)}.mkString("\n")
//      testPrintln(s"Hot nodes:\n $hotNodesString")
      val expensiveRuleString = stats.expensiveRules(5).map {case (n, s) => printRuleApplication(n, s)}.mkString("\n")
      testPrintln(s"Expensive rules:\n$expensiveRuleString\n")
      testPrintln(StopWatch.summary.toString)
    }

    def initCertTree(trace: ProofTrace): Unit = trace match {
      case trace: ProofTraceCert => CertTree.fromTrace(trace)
      case _ =>
    }

    sresult._1 match {
      case Nil =>
        // printStats(sresult._2)
        if (sresult._2.timedOut)
          throw SynTimeOutException(s"Timeout after ${(sresult._2.duration / 1000.0).round.toInt} seconds")
        else
          println("Failed to synthesise due to unrealizable spec or incompleteness")
          sys.exit(2)
          // throw SynthesisException(s"Failed to synthesise due to unrealizable spec or incompleteness")
      case procs =>
        for { sln <- procs } {
          val result = if (params.printSpecs) {
            sln.map(p => {
              val (pre, post) = (p.f.pre.pp.trim, p.f.post.pp.trim)
              List(pre, post, p.pp.trim).mkString("\n")
            }).mkString("\n")
          } else {
            sln.map(_.pp.trim).mkString("\n")
          }

          // [Certify] initialize and print cert tree
          initCertTree(synthesizer.trace)

          if (params.printStats) {
            testPrintln(s"\n[$testName]:", Console.MAGENTA)
            testPrintln(params.pp)
            testPrintln(s"${spec.pp}\n", Console.BLUE)
            testPrintln(s"Successfully synthesised in $duration milliseconds:", Console.GREEN)
            printStats(sresult._2)
            testPrintln(result)
            testPrintln("-----------------------------------------------------")
          } else {
            if (procs.length > 1)
              testPrintln("-----------------------------------------------------")
            println(result)
          }
          if (out != noOutputCheck) {
            val tt = out.trim.lines.map(_.trim)
            val res = result.trim.lines.map(_.trim)
            if (params.assertSuccess && !res.equals(tt)) {
              throw SynthesisException(s"\nThe expected output\n$tt\ndoesn't match the result:\n$res")
            }
          }
          if (params.interactive) {
            testPrintln(sresult._2.getExpansionChoices.mkString("\n"))
            testPrintln("-----------------------------------------------------")
          }
          if (params.certTarget != NoCert) {
            val certTarget = params.certTarget
            val targetName = certTarget.name
            val root = CertTree.root.getOrElse(throw SynthesisException("Search tree is uninitialized"))
            val tree = SuslikProofStep.of_certtree(root)
            val certificate = certTarget.certify(testName, procs.head.head, tree, root.goal, env)
            if (params.certDest == null) {
              testPrintln(s"\n$targetName certificate:", Console.MAGENTA)
              certificate.outputs.foreach(o => {
                testPrintln(s"File ${o.filename}:\n", Console.MAGENTA)
                testPrintln(s"${o.body}")
              })
            } else {
              certificate.outputs.foreach(o => {
                val path = Paths.get(params.certDest.getCanonicalPath, o.filename).toFile
                new PrintWriter(path) { write(o.body); close() }
                testPrintln(s"\n$targetName certificate exported to $path", Console.MAGENTA)
              })
            }
          }
        }
        procs
    }
  }

  def getDefs(defFiles: List[File]): String = {
    if (defFiles.isEmpty) return ""
    assert(defFiles.size == 1, "More than one file with definitions in the folder")
    val file = new File(defFiles.head.getAbsolutePath)
    readLines(file).mkString("\n")
  }

  def getDefsFromDir(dir: File): String = {
    if (dir.exists() && dir.isDirectory)
      getDefs(dir.listFiles.filter(f => f.isFile && f.getName.endsWith(s".$defExtension")).toList)
    else ""
  }

  def runAllTestsFromDir(dir: String) {
    val path = List(rootDir, dir).mkString(File.separator)
    val testDir = new File(path)
    if (testDir.exists() && testDir.isDirectory) {
      // Create log file
      SynStatUtil.init(defaultConfig)
      // Get definitions
      val defs = getDefsFromDir(testDir)
      // Get specs
      val tests = testDir.listFiles.filter(f => f.isFile
        && (f.getName.endsWith(s".$testExtension") ||
            f.getName.endsWith(s".$sketchExtension"))).toList
      for (f <- tests) {
        val (testName, desc, in, out, params) = getDescInputOutput(f.getAbsolutePath)
        val fullInput = List(defs, in).mkString("\n")
        doRun(testName, desc, fullInput, out, params)
      }
    }
  }

  def runSingleTestFromDir(dir: String, fname: String, params: SynConfig = defaultConfig) {
    var testDir = new File(dir)
    if (!testDir.exists()) {
      val path = List(rootDir, dir).mkString(File.separator)
      println(s"Trying the path $path")
      testDir = new File(path)
      if (!testDir.exists()) {
        System.err.println(s"Found no directory $dir.")
        return
      }
    }
    if (testDir.exists() && testDir.isDirectory) {
      // Maybe create log file (depending on params)
      SynStatUtil.init(params)
      // Get definitions
      val defs = getDefsFromDir(testDir)
      // Get specs
      val tests = testDir.listFiles.filter(f => f.isFile
        && (f.getName.endsWith(s".$testExtension") ||
            f.getName.endsWith(s".$sketchExtension"))).toList
      tests.find(f => f.getName == fname) match {
        case Some(f) =>
          val (testName, desc, in, out, allParams) = getDescInputOutput(f.getAbsolutePath, params)
          val fullInput = List(defs, in).mkString("\n")
          doRun(testName, desc, fullInput, out, allParams)
        case None =>
          System.err.println(s"No file with the name $fname found in the directory $dir.")
      }
    }
  }

  def readLines(file: File): List[String] =
    managed(Source.fromFile(file)).map(_.getLines.toList)
      .opt.get

  def removeSuffix(s: String, suffix: String): String = {
    if (s.endsWith(suffix)) s.substring(0, s.length - suffix.length) else s
  }

}


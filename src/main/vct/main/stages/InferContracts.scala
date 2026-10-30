package vct.main.stages

import com.typesafe.scalalogging.LazyLogging
import hre.debug.TimeTravel
import hre.debug.TimeTravel.CauseWithBadEffect
import hre.io.Readable
import hre.progress.Progress
import hre.stages.Stage
import vct.col.ast.{Program, SimplificationRule, Verification}
import vct.rewrite.lang.NoSupportSelfLoop
import vct.importer.{PathAdtImporter, Util}
import vct.col.ast._
import vct.col.rewrite.Generation
import vct.options.Options
import vct.options.types.{Backend, PathOrStd}
import vct.parsers.debug.DebugOptions
import vct.resources.Resources
import vct.result.VerificationError.SystemError
import java.nio.file.{Files,Path,Paths}
import scala.collection.mutable.ArrayBuffer
import scala.jdk.CollectionConverters._
import java.nio.charset.StandardCharsets
import vct.options.types.PathOrStd
import vct.col.print.Ctx
import vct.col.print.Doc
import scala.util.matching.Regex
import vct.col.origin.{SourceName,PositionRange}
import vct.col.rewrite.CleanForPrinting
import scala.sys.process._
import scala.util.chaining._
import hre.util.ScopedStack
import scala.util.control.Breaks._


object InferContracts extends LazyLogging {


  def ofOptions(options: Options): InferContracts =  new InferContracts(
    options.inputs,
    options.inferOutput,
    options.inferTriPath,
    options.inferVerbose,
    options.inferLoopContracts,
    options.inferInitGlobals
  )

}

/** 
    Infers contracts
  */
class InferContracts(
    val inputs: Seq[PathOrStd],
    val inferOutput: Option[Path],
    val inferTriPath: Option[Path],
    val inferVerbose: Boolean,
    val inferLoopContracts: Boolean,
    val inferInitGlobals: Boolean,

) extends Stage[Verification[_ <: Generation], Verification[_ <: Generation]]
    with LazyLogging {
  override def friendlyName: String = "InferContracts"
  override def progressWeight: Int = 10

  override def run(
      input: Verification[_ <: Generation]
  ): Verification[_ <: Generation] =
    runTyped(input)

  //I'm not sure how the generics are supposed to work but I'm pretty sure that I'm doing it wrong
  def runTyped[G <: Generation](
      input: Verification[G]
  ): Verification[G] ={
     val program: Program[G] = CleanForPrinting[G]().dispatch(input.tasks.head.program)
     val funcs: Seq[Procedure[G]] = program.declarations.collect{case node: Procedure[G] => node}
     val main:  Procedure[G] = program.declarations.collectFirst{case node: Procedure[G] if node.o.getPreferredNameOrElse().snake == "main" => node}
     .getOrElse(throw new NoSuchElementException("Missing input!"))
     
     val contractStarts: Seq[(String,Int)] = funcs.collect {
        case f: Procedure[G] if !getRealName(f).startsWith("__vercors_") => (getRealName(f), f.o.findAll[PositionRange].last.startLineIdx)
      }

     val loopStarts: ArrayBuffer[(Int,Int)] = (program.collect { case l: Loop[G] => 
      val start = l.o.findAll[PositionRange].last.startLineIdx 
        ((start,start))
     }).to(ArrayBuffer)

//     logger.info(contractStarts.map{case (name,start) => s"($name, $start)"}.mkString(","))

     val inputPath: Path = inputs(0).underlyingPath.getOrElse {
       throw new IllegalArgumentException(
         "InferContracts requires a file input, not stdin/stdout"
       )
      }
    
     // We replace the names in ctx (which are normalised) with the original names 
     val ctx = getNamedCtx(program)
     
     val harness: ArrayBuffer[String] = genHarness(ctx,main,removeContracts(contractStarts,loopStarts,getSource(inputPath))) 

     Files.write(Paths.get(s"harness_${inputPath.getFileName}"), harness.asJava, StandardCharsets.UTF_8)
    
     val triResult = runTri(inputPath)
     if(inferVerbose) logger.info(s"${triResult}")

     val inferred: Seq[(String, String, String)] = parseInferred(triResult)
     //logger.info(inferred.map{case (sort,name,contract) => s"($sort, $name, $contract)"}.mkString(","))

     val inferredMerge: Seq[(String,Int,String)] = 
      (getFuncStarts(contractStarts,inferred) ++ getLoopStarts(program, loopStarts.toSeq,inferred,ctx)).sortBy(_._2)

     val output: ArrayBuffer[String] = mergeContracts(inferredMerge,getSource(inputPath)) 
     
     val outputPath: Path = inferOutput.getOrElse(Paths.get(s"inferred_${inputPath.getFileName}"))
     Files.write(outputPath, output.asJava, StandardCharsets.UTF_8)

     input
  }

  def printType[G](t: Type[G], ctx: Ctx): String = t match {
    case p: PointerType[G]  => printType(p.element, ctx) + "*"
    case s: TByValueClass[G] => "struct " + s.toStringWithContext(ctx)
    case other               => other.toStringWithContext(ctx)
  }

  def getRealName[G](node:Node[G]): String = {
    node.o.find[SourceName].map(_.name).getOrElse(node.o.getPreferredNameOrElse().snake)
  }

  def getSource (inputPath: Path): ArrayBuffer[String] = Files.readAllLines(inputPath, StandardCharsets.UTF_8).asScala.to(ArrayBuffer)

  def getPredicateExprs[G](pred: AccountedPredicate[G]): Seq[Expr[G]] = pred match {
    case UnitAccountedPredicate(expr) => Seq(expr)
    case SplitAccountedPredicate(left, right) => getPredicateExprs(left) ++ getPredicateExprs(right)
  }
  
  def getNamedCtx[G](program: Program[G]): Ctx = {
    val namedCtx = Ctx(syntax = Ctx.C).namesIn(program)

    namedCtx.copy(names = namedCtx.names.map { 
       case (decl, _) => decl -> getRealName(decl)
     })
  }

  def genHarness[G](ctx: Ctx, main: Procedure[G], lines: ArrayBuffer[String] ): ArrayBuffer[String] = {
    val requires: AccountedPredicate[G] = main.contract.requires
    val ensures: AccountedPredicate[G] = main.contract.ensures
    
    val oldReplacements: Seq[(String,String)] = List(requires,ensures).flatMap(getPredicateExprs).flatMap(collectOlds).collect{
      case node: Old[G] => (node.toStringWithContext(ctx),fixOld(node,ctx))
    }
     

    lines += "\n void harness_main()"
    lines += "{"

    //assume
    lines ++= printPredicate(ctx,requires,oldReplacements,"assume")

    main.returnType match {
      case _: TVoid[G] => lines += "\tmain();"
      case other       => lines += s"\t${printType(main.returnType,ctx)} main_result = main();"
    }
    
    //assert
    lines ++= printPredicate(ctx,ensures,oldReplacements,"assert")

    lines += "}"
  }

  def runTri(inputPath: Path): String = {
     val triPath: String = inferTriPath.map(_.toString).getOrElse("tri")
     val loopOption: String = if(inferLoopContracts) "-inv" else ""
     val globalOption: String = if(inferInitGlobals) "-forceNondetInit" else ""
     s"${triPath} harness_${inputPath.getFileName} -acsl ${loopOption} -m:harness_main ${globalOption}".!!
  }


  def parseInferred(s: String): Seq[(String, String, String)] =
    s.split("\\*/").map(_.trim).filter(_.contains("/*")).grouped(2).collect {
      case Array(header, body) =>
        val h = header.dropWhile(_ != '*').drop(1).trim
        
        val sort = if (h.startsWith("contract for ")) "func" else "loop"
        
        val name = if (h.startsWith("contract for ")) h.stripPrefix("contract for ")
                   else "loop_" + h.split(" ").last

        (sort, name, (body + "\n*/")) 
  }.toList

  def getFuncStarts(contractStarts: Seq[(String,Int)], inferred: Seq[(String,String,String)]): Seq[(String,Int,String)] = {
    val contractStartsMap: Map[String,Int] = contractStarts.toMap
    val inferredFuncStarts: Seq[(String,Int,String)] = getFuncInferred(inferred).collect {
      case (sort,name,contract) if contractStartsMap.contains(name) => (sort,contractStartsMap(name),acslToVc(contract))
    }
  //logger.info(inferredFuncStarts.map{case (sort,start,contract) => s"($sort, $start, $contract)"}.mkString(","))
   inferredFuncStarts
  }

  def getLoopStarts[G](program: Program[G], loopStarts: Seq[(Int,Int)], inferred: Seq[(String,String,String)], ctx: Ctx): Seq[(String,Int,String)]  = {
    val loopStartsMap: Map[Int,Int] = loopStarts.toMap
    val inferredLoopStarts: Seq[(String,Int,String)] = getLoopInferred(inferred).collect {
      case (sort,name,contract) if loopStartsMap.contains(name.split("_").last.toInt + - 2) => 
        val start = loopStartsMap(name.split("_").last.toInt - 2)
        (sort,start,loopToVc(program,start,contract,ctx))
    } // -2 Because line number from tricera is one ahead, plus we are zero indexed so plus another 1
    //logger.info(inferredLoopStarts.map{case (sort,start,contract) => s"($sort, $start, $contract)"}.mkString(","))
    inferredLoopStarts
  }

  def getFuncInferred(contracts: Seq[(String, String, String)]): Seq[(String, String, String)] =
    contracts.filter{contract => contract._1 == "func"}

  def getLoopInferred(contracts: Seq[(String, String, String)]): Seq[(String, String, String)] =
    contracts.filter{contract => contract._1 == "loop"}

  def loopToVc[G](program: Program[G], loop: Int, contract: String, ctx: Ctx):  String = {
      val atPre: Regex = """\\at\((\w+), Pre\)""".r
      val invariant: String = contract.linesIterator.find(_.trim.startsWith("loop invariant")).get.trim

      var preVars = Set.empty[String]

      val cleanInvariant: String = atPre.replaceAllIn(invariant, m => {
        preVars += m.group(1)
        s"pre_${m.group(1)}"
      }).replace("loop invariant","loop_invariant")

      // We have to add ghost variables for each variable that was in at()
      preVars.foldLeft(""){
        case (ghostLines,loopVar) =>  s"$ghostLines//@ ghost ${getLoopVarType(program,loop,loopVar,ctx)} pre_${loopVar} = ${loopVar};\n"
      }.concat(s"//@${cleanInvariant}")
    
    }

  def getLoopVarType[G](program: Program[G],loop: Int, loopVar: String, ctx: Ctx): String = {
    var vars: ScopedStack[ArrayBuffer[(String,Type[G])]] = ScopedStack()
    var foundVar: Option[Type[G]] = None

    //We have to search the tree for the scope of the loop to be able to get the type for ghost vars
    def visit(n: Node[G]): Unit = n match {
      case s@Scope(v, body) =>
        vars.having(ArrayBuffer()) { 
          visit(body) 
        }

      case LocalDecl(v) =>
        vars.top += ((getRealName(v),v.t))

      case HeapLocalDecl(v) =>
        vars.top += ((getRealName(v),v.t))

      case v: HeapVariable[G] =>
        vars.top += ((getRealName(v),v.t))

      case l: Loop[G] =>
        if (l.o.findAll[PositionRange].last.startLineIdx == loop) { 
          foundVar = vars.toSeq.flatten.find(_._1 == loopVar).map(_._2)
          break()
        }

      case other =>
        other.subnodes.foreach(visit) 
    }

    breakable {
      vars.having(ArrayBuffer()) {  // for globals
        visit(program)
      }
    }
    def unwrapElement[G](t: Type[G]): Type[G] = t match {
      case TNonNullPointer(element, _) => element
      case other => other
    }

    foundVar.map(unwrapElement).map(t => printType(t,ctx)).getOrElse("")

  }

  def acslToVc(contract: String):  String = fixAcslValid(fixAcslOld(replaceAcslBool(contract)))

  def replaceAcslBool(contract: String): String = {
    val unqoutedBool = """"[^"]*"|(\\true)|(\\false)""".r

    unqoutedBool.replaceAllIn(contract, m => {
      if (m.group(1) != null) "true"        
      else if (m.group(2) != null) "false"   
      else m.matched 
    })
  }

def fixAcslValid(contract: String): String = {
  val valid = """\\valid\(([\w->*.]+)\)""".r
  val newPerms = scala.collection.mutable.LinkedHashSet[String]()

  val body = contract.split("\n", -1).map { line =>
    val t = line.trim
    val kind = if (t.startsWith("requires")) "requires" else if (t.startsWith("ensures")) "ensures" else ""
    if (kind.isEmpty) line
    else valid.replaceAllIn(line, m => {
      newPerms += s"$kind \\pointer_index(${m.group(1)},0,write);"
      java.util.regex.Matcher.quoteReplacement(s"(${m.group(1)} != NULL)")
    })
  }.mkString("\n")

  val toAdd = newPerms.filterNot(body.contains)
  if (toAdd.isEmpty) body else body.replace("/*@", "/*@\n" + toAdd.mkString("\n") + "\n")
}
  
  def fixAcslOld(contract: String): String = {
    val old = """"[^"]*"|\\old\((\w+)\)\.(\w+)""".r
    old.replaceAllIn(contract, m => {
      if (m.group(1) != null && m.group(2) != null) Regex.quoteReplacement(s"\\old(${m.group(1)}.${m.group(2)})")     
      else m.matched 
    })
  }

  def removeContracts(contractStarts: Seq[(String,Int)], loopStarts: ArrayBuffer[(Int,Int)], lines: ArrayBuffer[String]): ArrayBuffer[String] = {
      contractStarts.sortBy(_._2)(Ordering.Int.reverse).foldLeft(lines){
          case (result, (name, start)) =>
            
            //Remove rest of contract only if original contract is not one line
            if (result(start).contains("/*@")) {
              if(!result(start).contains("*/")) {
              
                val contractLength = lines.view.drop(start+1).indexWhere(_.contains("*/")) + 1
                val contractEndIndex = start + contractLength
                
                result(contractEndIndex) = result(contractEndIndex).drop(result(contractEndIndex).indexOf("*/")+2)
                if (result(contractEndIndex) == "") result.remove(contractEndIndex,1)

                result.remove(start+1,contractLength - 1)
                result(start) = result(start).take(result(start).indexOf("/*@"))
                updateLoops(loopStarts,start,(-1 * contractLength))
              } else {
                result(start) = result(start).take(result(start).indexOf("/*@")) + result(start).drop(result(start).indexOf("*/") + 2)
              }

              if(name != "main") {
                result.insert(start+1,"/*@contract@*/")
                updateLoops(loopStarts,start,1)
              }

            }
            else {
              if(name != "main") result.insert(start,"/*@contract@*/")
              updateLoops(loopStarts,start,1)
            }


            result
      }.mapInPlace(_.replaceAll("""//@.*""", ""))
      
  }

  def updateLoops(loopStarts: ArrayBuffer[(Int,Int)], start: Int, change: Int): ArrayBuffer[(Int,Int)] = loopStarts.mapInPlace {
    case (current, original) if current >= start => (current + change, original)
    case other => other
  }
    
  def mergeContracts(inferredContractStarts: Seq[(String,Int,String)], lines: ArrayBuffer[String]): ArrayBuffer[String] = {
      inferredContractStarts.sortBy(_._2)(Ordering.Int.reverse).foldLeft(lines){
          case (result, ("func", start, contract)) =>
            logger.info(s"Merging $contract at $start ")
            //mergeFuncContract(contract, start, result)          
          case (result, ("loop", start, contract)) =>
            //logger.info(s"Merging $contract at $start ")
            mergeLoopContract(contract, start, result)          
      }
      
  } 
def mergeFuncContract(contract: String, start: Int, lines: ArrayBuffer[String]): ArrayBuffer[String] = {
  if (lines(start).contains("/*@")) {
    val contractLines = contract.linesIterator.map(_.trim).toSeq
    val requires = contractLines.filter(_.startsWith("requires"))
    val ensures  = contractLines.filter(_.startsWith("ensures"))

    val bodyStart = start + 1
    val closeIdx  = lines.indexWhere(_.contains("*/"), bodyStart) 
    val body      = lines.slice(bodyStart, closeIdx)

    val lastRequires  = body.lastIndexWhere(_.trim.startsWith("requires"))
    val firstEnsures  = body.indexWhere(_.trim.startsWith("ensures"))
    val lastEnsures   = body.lastIndexWhere(_.trim.startsWith("ensures"))

    val requiresInsert =
      if (lastRequires >= 0) bodyStart + lastRequires + 1
      else if (firstEnsures >= 0) bodyStart + firstEnsures
      else closeIdx

    val ensuresInsert =
      if (lastEnsures >= 0) bodyStart + lastEnsures + 1
      else closeIdx

    lines.insertAll(math.max(ensuresInsert, requiresInsert), ensures)
    lines.insertAll(requiresInsert, requires)
  } else {
    lines.insert(start, contract)
  }

  lines
}

    def mergeLoopContract(contract: String, start: Int, lines: ArrayBuffer[String]): ArrayBuffer[String] = {
      if (lines(start).contains("//@")) {
        val ghostLines: Seq[String] = contract.linesIterator.map(_.trim).filter(_.startsWith("//@ ghost")).toSeq
        val invariants: Seq[String] = contract.linesIterator.drop(ghostLines.length).toSeq

        val contractLength = lines.view.drop(start+1).indexWhere(line => !line.contains("*/")) + 1

        lines.insert(start + contractLength,invariants.mkString)
        lines.insert(start,ghostLines.mkString)

      } else {
        lines.insert(start, contract)
      }

      lines
  }

  def collectOlds[G](n: Node[G]): Seq[Old[G]] = (n match {
    case old: Old[G] => Seq(old)
    case _ => Seq()
  }) ++ n.subnodes.flatMap(collectOlds)

  def fixOld[G](old: Old[G], ctx: Ctx): String = {
    val printedInner = old.expr.toStringWithContext(ctx)      
    val castType = printType(old.expr.t,ctx)
    s"$$at(\"Old\", ($castType)($printedInner))"
  }

  def cleanPredicates(oldReplacements: Seq[(String,String)], s: String): String = {
    val oldReplaced = oldReplacements.foldLeft(s) { case (acc, (old, replacement)) =>acc.replace(old, replacement)}
    oldReplaced.replaceAll("""\btrue\b""","(1 != 0)")
      .replaceAll("""\bnull\b""","0")
      .replaceAll("""\\result\b""","main_result")
      .replaceAll("""\\pointer_index\(([^,()]+?), [^,()]+, [^()]*\)""", "($1 != 0)")


    
  }

  def printPredicate[G](ctx: Ctx, predicate: AccountedPredicate[G], oldReplacements: Seq[(String,String)], name: String): ArrayBuffer[String] =
    getPredicateExprs(predicate).foldLeft(ArrayBuffer[String]()) {
      case(lines,pre) =>
        lines += s"${name}(${cleanPredicates(oldReplacements,pre.toStringWithContext(ctx))});" 
        lines
     }

}


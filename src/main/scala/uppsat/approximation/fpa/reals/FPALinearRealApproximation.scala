package uppsat.approximation.fpa.reals

import uppsat.approximation._

import uppsat.ast.AST.Label
import uppsat.approximation.components._
import uppsat.approximation.codec._
import uppsat.theory.FloatingPointTheory._
import uppsat.Timer
import uppsat.ModelEvaluator.Model
import uppsat.precision.PrecisionMap.Path
//import uppsat.Encoder.PathMap
import uppsat.theory.FloatingPointTheory.FPSortFactory.FPSort
import uppsat.precision.IntPrecisionOrdering
import uppsat.precision.PrecisionMap
import uppsat.theory.FloatingPointTheory
import uppsat.ModelEvaluator
import uppsat.ast.AST
import uppsat.ast._
import uppsat.solver.Z3Solver
import uppsat.solver.Z3OnlineSolver
import uppsat.theory.BooleanTheory.BoolTrue
import uppsat.theory.BooleanTheory.BoolFalse
import uppsat.theory.BooleanTheory
import uppsat.theory.BooleanTheory.BooleanFunctionSymbol
import uppsat.theory.BooleanTheory.BooleanConstant
import uppsat.theory.BooleanTheory.BoolVar
import uppsat.ModelEvaluator.Model
import uppsat.solver.Z3OnlineException
import uppsat.solver.Z3OnlineSolver
import uppsat.globalOptions
import uppsat.theory.RealTheory._
import uppsat.theory.RealTheory
import uppsat.approximation.reconstruction.EqualityAsAssignmentReconstruction
import uppsat.approximation.refinement.UniformRefinementStrategy
import uppsat.approximation.reconstruction.EmptyReconstruction
import uppsat.approximation.reconstruction.PostOrderReconstruction

trait FPALinRealContext extends ApproximationContext {
  type Precision = Int
  val precisionOrdering = new IntPrecisionOrdering(0, 1)
  val inputTheory = FloatingPointTheory
  val outputTheory = RealTheory
  //TODO
  var oldModel = List() : List[(RealVar,Double)]
}

trait FPALinRealCodec extends FPALinRealContext with PreprocessingPostOrderCodec {
  // Encodes a node by scaling its sort based on precision and calling
  // cast to ensure sortedness.
  var fpToRealMap = Map[ConcreteFunctionSymbol, ConcreteFunctionSymbol]()
  var degree = Map[uppsat.ast.AST.Label, List[(Double,List[(FPVar,Int)])]]()

  def cast(ast : AST, newSort : ConcreteSort) = {
    if (ast.symbol.sort == newSort)
      ast
    else {
      newSort match {
        case FPSort(s,e) =>
          AST(RealToFPFactory(newSort), List(), List(ast))
        case RealSort =>
          AST(FPToRealFactory(ast.symbol.sort), List(), List(ast))
      }
    }
  }

  //return true and the index of a variable if it exist in the list
  // false and -1 otherwise
  def existVarIndex(lst : List[(FPVar,Int)], fpVar : FPVar) : (Boolean, Int) = {
    var result = (false, -1)
    var count = 0
    for (n <- lst) {
      if (n._1 == fpVar){
        result = (true, count)
      }
      count += 1
    }
    result
  }

  def getApproxValue(variable : RealVar, lst : List[(RealVar, Double)]) : Double = {
    var result = 1.0 : Double
    for (n <- lst) {
      if (n._1 == variable){
        result = n._2
      }
    }
    result
  }

  // Encode FP by precision value:
  // 0 - Replace FP constraints with corresponding Real constraints
  // 1 - Introduce \epsilon > 0  as buffer in constraints to avoid rounding disrupting model reconstruction
  // 3 - No encoding, retain FP constraints
  import BigInt._;
  
  def preprocess(ast : AST) = {
    degree = AST.postVisit(ast, Map[uppsat.ast.AST.Label, List[(Double,List[(FPVar,Int)])]](), mapNode)
  }
  
  def mapNode(degree : Map[uppsat.ast.AST.Label, List[(Double,List[(FPVar,Int)])]],ast : AST) : Map[uppsat.ast.AST.Label, List[(Double,List[(FPVar,Int)])]] = {
    val AST(symbol, label, children) = ast
    val nLab = label
    
    if (degree contains nLab) {throw new Exception("Label in Map")}
    symbol match{
    // single variable
    case fpvar : FPVar =>
      degree + (nLab -> List((1.0, List((fpvar, 1)))))
    // single literal
    case fplit: FloatingPointLiteral =>
      var toDouble = bitsToDouble(fplit)
      degree + (nLab -> List((toDouble, List((null, 0)))))

    // functionSymbols
    case fpSym : FloatingPointFunctionSymbol =>
        var c = List() : List[List[(Double,List[(FPVar,Int)])]]
        for (n <- children){
          val childLabel = n.label
          if((degree get childLabel) != None){
            c = degree(childLabel) :: c
          }
        }
        //val child1 = children(1).label
        //val child2 = children(2).label
        fpSym.getFactory match {
        // multiplicattion
          case FPMultiplicationFactory =>
            val childLst1 = c(0)
            val childLst2 = c(1)
            var newLst = List() : List[(Double,List[(FPVar,Int)])]

            for (n <- childLst1){
              var lit = n._1
              var varsN = n._2
              
              for (m <- childLst2){
                lit = m._1 * lit
                var varsM = m._2
                var tmpLst = List() : List[(FPVar,Int)]
                tmpLst = varsN

                for (m1 <- varsM){
                  var fpVar = m1._1
                  var existVar = existVarIndex(tmpLst, fpVar)
                  var exist = existVar._1
                  var index = existVar._2

                  if (exist){
                    var newDegr = m1._2 + (tmpLst(index)._2)
                    var newTup = (fpVar, newDegr)
                    tmpLst = tmpLst.updated(index, newTup)
                  }else{
                    tmpLst = m1 +: tmpLst
                  }
                }
                // fullösning
                tmpLst = tmpLst.filter(_ != (null,0))
                newLst = (lit, tmpLst) +: newLst
              }
            }
            degree + (nLab -> newLst)

          // division
          case FPDivisionFactory =>
            val childLst1 = c(0)
            val childLst2 = c(1)
            var newLst = List() : List[(Double,List[(FPVar,Int)])]

            for (n <- childLst1){
              var lit = n._1
              var varsN = n._2
              
              for (m <- childLst2){
                lit = m._1 * lit
                var varsM = m._2
                var tmpLst = List() : List[(FPVar,Int)]
                tmpLst = varsN

                for (m1 <- varsM){
                  var fpVar = m1._1
                  var existVar = existVarIndex(tmpLst, fpVar)
                  var exist = existVar._1
                  var index = existVar._2

                  if (exist){
                    var newDegr = (tmpLst(index)._2) - m1._2
                    var newTup = (fpVar, newDegr)
                    tmpLst = tmpLst.updated(index, newTup)
                  }else{
                    var newDegr = -m1._2
                    var newTup = (fpVar, newDegr)
                    tmpLst = newTup +: tmpLst
                  }
                }
                // fullösning
                tmpLst = tmpLst.filter(_ != (null,0))
                newLst = (lit, tmpLst) +: newLst
              }
            }
            degree + (nLab -> newLst)

          // addition
          case FPAdditionFactory =>
            val childLst1 = c(0)
            val childLst2 = c(1)
            var newLst =  childLst1 ++ childLst2
            degree + (nLab -> newLst)
          // other functionSymbols
          case _ =>
            degree
            //println("other functionsymbol")
        }
      case _ =>
        degree
    }
  }

  def encodeNode(symbol : ConcreteFunctionSymbol, label : Label, children : List[AST], precision : Int) : AST = {
    symbol match{
      case fpPred : FloatingPointPredicateSymbol =>
        val childLst1 = degree(children(0).label)
        val childLst2 = degree(children(1).label)
        val childs = List(childLst1, childLst2)

        val newSymbol = fpPred.getFactory match {
          case FPEqualityFactory => RealEquality
          case FPFPEqualityFactory => RealEquality
          case FPLessThanFactory => RealLT
          case FPLessThanOrEqualFactory => RealLEQ
          case FPGreaterThanFactory => RealGT
          case FPGreaterThanOrEqualFactory => RealGEQ
          case _ => throw new Exception(fpPred + " unsupported")
        }

        // common fun - returns the GCD of a childLst
        var newChildren = List() : List[AST]
        for(m <- childs){
          var polLst = List() : List[AST]
          for (n <- m){
            var lit = n._1
            var lst = n._2
            var len = lst.length
            var x = 0
            var const = 1.0 : Double
            if (len > 1){
              for(x <- 0 to (len-1)){
                var elem = lst(x)
                var variable = new RealVar(elem._1.name)
                var degree = elem._2
                if(!oldModel.isEmpty){
                  const = const * scala.math.pow(getApproxValue(variable, oldModel), degree)
                }
              }
            }
            var elem = lst.last
            if(elem._1 == null){
              var litLeaf = Leaf(RealNumeral((lit.toInt) : BigInt))
              polLst = litLeaf +: polLst
            }else{
              var variable = new RealVar(elem._1.name)
              var degree = elem._2
              if(!oldModel.isEmpty){
                const = const * scala.math.pow(getApproxValue(variable, oldModel), degree)
              }
              var litLeaf = Leaf(RealNumeral((const * lit).toInt : BigInt)) //problably not correct way
              var varLeaf = Leaf(variable)
              var subTree = realMultiplication(litLeaf, varLeaf)
              polLst = subTree +: polLst
              //aprox lats var here
            }
          }
          var ast : AST = polLst.head
          if(polLst.length > 1){
            var lstHead = polLst.head
            var lstTail = polLst.tail
            ast = lstTail.foldLeft(lstHead){(acc,i)=>realAddition(acc,i)}
            newChildren = ast +: newChildren
          }else{
            newChildren = ast +: newChildren
          }
        }
        // uses floating point literal
        val newAST : AST = AST(newSymbol, List(), newChildren)
        newAST
      // other Symbol
      case _ =>
        //println("other symbol")
    }
    
    // my mods/\


    val (newSymbol, newLabel, newChildren) : (ConcreteFunctionSymbol, Label, List[AST]) =
      precision match {
        case precisionOrdering.maximalPrecision =>
          (symbol, label, children)

        case 0 =>
          symbol match {
            case fpVar : FPVar => {
              if (!fpToRealMap.contains(fpVar)) {
                fpToRealMap = fpToRealMap + (fpVar ->  new RealVar(fpVar.name))
              }
              (fpToRealMap(fpVar), label, children)
            }

            case fpLit : FloatingPointLiteral => {
              fpLit.getFactory match {
                case FPNegativeZero => {
                  (RealNumeral(0), label, children)
                }
                case FPPositiveZero => {
                  (RealNumeral(0), label, children)
                }
                case FPPlusInfinity => {
                  (RealNumeral(2.pow(53) + 1), label, children) // TODO: fix magic constants
                }

                case FPMinusInfinity => {
                  (RealNumeral(-(2.pow(53) + 1)), label, children) // TODO: fix magic constants
                }

                case FPConstantFactory(sign, ebits,  sbits) => {
                  val exp = (sbits.length + 1 - (ebitsToInt(ebits)))

                  val num = if (exp > 0) {
                    BigInt(bitsToInt((1::sbits) ++ (List.fill(exp)(0))))
                  } else { 
                    BigInt(bitsToInt(1::sbits))
                  }

                  val denom = if (exp > 0) {
                    BigInt(1)
                  } else {
                    BigInt(1) << (- exp)
                  }

                  (RealDecimal(num, denom), label, children)
                }
              }
            }

            case fpSym : FloatingPointFunctionSymbol => {
              var nChildren = if (children.head.symbol.sort == RoundingModeSort) children.tail
                                else children

              var nLabel = label
              val newSymbol = fpSym.getFactory match {
                case FPNegateFactory   => RealNegation
                case FPAdditionFactory => RealAddition
                case FPSubstractionFactory => RealSubstraction
                case FPMultiplicationFactory => RealMultiplication
                case FPDivisionFactory => RealDivision
                case FPToFPFactory => val r = nChildren(0).symbol
                  nLabel = nChildren(0).label
                  nChildren = nChildren(0).children
                  r
                case _ => throw new Exception(fpSym + " unsupported")
              }
              (newSymbol, nLabel, nChildren)
            }
            case fpPred : FloatingPointPredicateSymbol => {
              val newSymbol = fpPred.getFactory match {
                case FPEqualityFactory => RealEquality
                case FPFPEqualityFactory => RealEquality
                case FPLessThanFactory => RealLT
                case FPLessThanOrEqualFactory => RealLEQ
                case FPGreaterThanFactory => RealGT
                case FPGreaterThanOrEqualFactory => RealGEQ
                case _ => throw new Exception(fpPred + " unsupported")
              }
              (newSymbol, label, children)
            }
            case _ => {
              (symbol, label, children)
            }
          }

        case _  =>
          (symbol, label, children)
      }


    val sortedChildren =
      for (i <- newChildren.indices)
      yield
          cast(newChildren(i), newSymbol.args(i))

    AST(newSymbol, newLabel, sortedChildren.toList)
  }

  // Describes translation of smallfloat values into values of the original formula.  
  def decodeSymbolValue(symbol : ConcreteFunctionSymbol, value : AST, p : Int) = {
    (symbol.sort, value.symbol) match {
      case (FPSort(e, s), RealZero) => {
          Leaf(FPPositiveZero(FPSort(e, s)))       
      }

      // TODO:  unify these two cases 
      case ( fpsort : FPSort, realValue : RealDecimal) => {
        val value = (BigDecimal(realValue.num) / BigDecimal(realValue.denom))
        if (value.abs >= BigDecimal(2.pow(53) + 1))
          if (value > 0)
            (Leaf(FPPlusInfinity(fpsort)))
          else
            (Leaf(FPMinusInfinity(fpsort)))
          else
            fpToAST(value.toDouble, fpsort)
      }

      case ( fpsort : FPSort, realValue : RealNumeral) => {
        val value = (BigDecimal(realValue.num) / BigDecimal(realValue.denom))
        if (value.abs >= BigDecimal(2.pow(53) + 1))
          if (value > 0)
            (Leaf(FPPlusInfinity(fpsort)))
          else
            (Leaf(FPMinusInfinity(fpsort)))
          else
            fpToAST(value.toDouble, fpsort)
      }
      
      case _ => value
    }
  }
  
  def retrieveFromAppModel(ast : AST, appModel : Model) = {
    if (appModel.contains(ast)) {
      appModel(ast)
    } else if (ast.isVariable && fpToRealMap.contains(ast.symbol)) {
      appModel(Leaf(fpToRealMap(ast.symbol), List()))
    }
    else if ( ast.symbol.isInstanceOf[FPFunctionSymbol] &&
              ast.symbol.asInstanceOf[FPFunctionSymbol].getFactory == FPToFPFactory)
      ast
    else
      throw new Exception("Node " + ast + " does not have a value in \n" + appModel.subexprValuation + "\n" + appModel.variableValuation )
  }

  // decodes values associated with nodes in the formula.
  def decodeNode( args : (Model, PrecisionMap[Precision]), decodedModel : Model, ast : AST) : Model = {
    val appModel = args._1
    val pmap = args._2
    
    val appValue = retrieveFromAppModel(ast, appModel)
    
    val decodedValue = decodeSymbolValue(ast.symbol, appValue, pmap(ast.label))
  
    if (decodedModel.contains(ast)){
      val existingValue = decodedModel(ast).symbol
      if ( existingValue != decodedValue.symbol) {
        ast.prettyPrint("\t")
        throw new Exception("Decoding the model results in different values for the same entry : \n" + existingValue + " \n" + decodedValue.symbol)
      }
    } else {
      if (ast.isVariable){
        println(">> "+ ast.symbol + " " + decodedValue.symbol + " /" + appValue.symbol +"/")
        val lst = List() : List[(ConcreteFunctionSymbol, AST)]
        //println(ModelEvaluator.evalAST(ast, ast.symbol, lst, inputTheory))
      }
      decodedModel.set(ast, decodedValue)
    }
    decodedModel
  }
}


trait FPALinRealRefinementStrategy extends FPALinRealContext with UniformRefinementStrategy {
  def increasePrecision(p : Precision) = {
    precisionOrdering.+(p, 1)

  }
}

object FPALinRealApp extends FPALinRealContext 
                  with FPALinRealCodec
                  with EqualityAsAssignmentReconstruction
                  with FPALinRealRefinementStrategy {
}

object FPALinRealNodeByNodeApp extends FPALinRealContext 
                  with FPALinRealCodec
                  with PostOrderReconstruction
                  with FPALinRealRefinementStrategy {
}

object FxPntFPALinRealApp extends FPALinRealContext 
                  with FPALinRealCodec
                  with FixpointReconstruction
                  with FPALinRealRefinementStrategy {
}

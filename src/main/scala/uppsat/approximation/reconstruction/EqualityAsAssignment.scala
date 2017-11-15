package uppsat.approximation.reconstruction



import uppsat.globalOptions._
import uppsat.approximation.ModelReconstruction
import scala.collection.mutable.{ListBuffer, Set}
import uppsat.ast.ConcreteFunctionSymbol
import scala.collection.mutable.{HashMap, MultiMap}

import uppsat.ast.AST
import uppsat.ast.IndexedFunctionSymbol

import uppsat.ModelEvaluator
import uppsat.ModelEvaluator.Model

import uppsat.theory.FloatingPointTheory
import uppsat.theory.BooleanTheory._
import uppsat.theory.BooleanTheory.BoolEquality
import uppsat.theory.IntegerTheory.IntEquality
import uppsat.theory.FloatingPointTheory.RoundingModeEquality
import uppsat.theory.FloatingPointTheory.FPPredicateSymbol
import uppsat.theory.FloatingPointTheory.FPEqualityFactory
import uppsat.theory.FloatingPointTheory.FPFPEqualityFactory
import uppsat.theory.FloatingPointTheory.FPSortFactory.FPSort

import uppsat.approximation.toolbox.Toolbox

import scala.collection.mutable.Queue
import scala.collection.mutable.Stack
import uppsat.theory.FloatingPointTheory.FloatingPointPredicateSymbol


trait EqualityAsAssignmentReconstruction extends ModelReconstruction {
  
  def trySet(lhs : AST, rhs : AST, candidateModel : Model) : Boolean = {
    val lhsDefined = candidateModel.contains(lhs)
    val rhsDefined = candidateModel.contains(rhs)
  
    val ret = 
      (lhs.isVariable, rhs.isVariable) match {
        case (true, true) => {
          (lhsDefined, rhsDefined) match {
            case (false, true) => {
              verbose(">> " + lhs.symbol + " " + lhs.label + " " + " <- " + candidateModel(rhs).symbol + "/" + rhs.symbol + " " + rhs.label + "/")  
              candidateModel.set(lhs, candidateModel(rhs))
              true
            }
            case (true, false) => {
              verbose(">> " + rhs.symbol + " " + rhs.label + " " + " <- " + candidateModel(lhs).symbol + "/" + lhs.symbol + " " + lhs.label + "/")
              candidateModel.set(rhs, candidateModel(lhs))
              true
            }
            case (false, false) => {
              false
            }
            case (true, true) => {
              false
            }
          }
        }
        case (true, false) if (!lhsDefined) => {
          verbose(">> " + lhs.symbol + " " + lhs.label + " " + " <- " + candidateModel(rhs).symbol + "/" + rhs.symbol + " " + rhs.label + "/")
          candidateModel.set(lhs, candidateModel(rhs))
          true
        }
        case (false, true) if (!rhsDefined) =>{
          verbose(">> " + rhs.symbol + " " + rhs.label + " " + " <- " + candidateModel(lhs).symbol + "/" + lhs.symbol + " " + lhs.label + "/")
          candidateModel.set(rhs, candidateModel(lhs))
          true
        }
        case (_, _) => {
          false
        }
    }
    ret
    
  }
  
  def equalityAsAssignment2(ast : AST, decodedModel : Model,  candidateModel : Model) : Boolean = {
    val ret = 
      if (ast.symbol.sort == BooleanSort && decodedModel(ast).symbol == BoolTrue) { 
        ast.symbol match {
          case RoundingModeEquality => trySet(ast.children(0), ast.children(1), candidateModel)
          case fpPred : FPPredicateSymbol => trySet(ast.children(0), ast.children(1), candidateModel)
          case idxSym : IndexedFunctionSymbol => 
            if (idxSym.getFactory == FPEqualityFactory || idxSym.getFactory == FPFPEqualityFactory)
              trySet(ast.children(0), ast.children(1), candidateModel)
            else
              false
//          case BoolEquality => trySet(ast.children(0), ast.children(1), candidateModel)
          case other => false
        } 
      } else {
        false
      }
    if (ret) {
      verbose("> " + ast.symbol + " " + ast.label + " " + " <- " + BoolTrue)
      candidateModel.set(ast, BoolTrue)
    }
    ret
  }

  
 def equalityAsAssignment(ast : AST, decodedModel : Model,  candidateModel : Model) : Boolean = { 
    ast match { 
      //        case AST(BoolEquality, _, _) | 
      //             AST(IntEquality, _, _)| 
      case AST(RoundingModeEquality, _ , _)| 
          AST(_: FPPredicateSymbol, _, _) 
          if (decodedModel(ast).symbol == BoolTrue && 
                (! ast.symbol.isInstanceOf[IndexedFunctionSymbol] 
                   || ast.symbol.asInstanceOf[FPPredicateSymbol].getFactory == FPEqualityFactory 
                   || ast.symbol.asInstanceOf[FPPredicateSymbol].getFactory == FPFPEqualityFactory)) => { 
            val lhs = ast.children(0) 
            val rhs = ast.children(1) 
            val lhsDefined = candidateModel.contains(lhs) 
            val rhsDefined = candidateModel.contains(rhs) 
 
            (lhs.isVariable, rhs.isVariable) match { 
              case (true, true) => { 
                (lhsDefined, rhsDefined) match { 
                  case (false, true) => candidateModel.set(lhs, candidateModel(rhs)) 
                    true 
                  case (true, false) => candidateModel.set(rhs, candidateModel(lhs)) 
                    true 
                  case (false, false) => false 
                  case (true, true) => false 
                } 
              } 
              case (true, false) if (!lhsDefined) => { 
                candidateModel.set(lhs, candidateModel(rhs)) 
                true 
              } 
              case (false, true) if (!rhsDefined) =>{ 
                candidateModel.set(rhs, candidateModel(lhs)) 
                true 
              } 
              case (_, _) => false 
            }
        }
      case _ => false
    }
 }
            
            
  
  def reconstructNode( decodedModel  : Model, candidateModel : Model, ast : AST) : Model = {
    val AST(symbol, label, children) = ast
    if (children.length > 0 && !equalityAsAssignment(ast, decodedModel, candidateModel)) {
      val newChildren = for ( c <- children) yield {
        Toolbox.getCurrentValue(c, decodedModel, candidateModel)
      }

      
      val newAST = AST(symbol, label, newChildren.toList)
      val newValue = ModelEvaluator.evalAST(newAST, inputTheory)
      verbose(ast.symbol + " " + ast.label + " " + " <- " + newValue.symbol)
      
      candidateModel.set(ast, newValue)      
      ast.ppWithModels("", decodedModel, candidateModel, false)
//      println("-----------------")
    }
    candidateModel
  }
  
  def reconstructSubtree(ast : AST, decodedModel : Model, candidateModel : Model) : Model = {
    AST.postVisit[Model, Model](ast, candidateModel, decodedModel, reconstructNode)
    candidateModel
  }
  
  
  def reconstruct(ast : AST, decodedModel : Model) : Model = {
    val candidateModel = new Model()
    
    val todo = new Stack[AST]()
    val toEvaluateEquality = ListBuffer() : ListBuffer[AST]
    val toEvaluateBoolean = new Stack[AST]()
    val toReconstructPredicate = new Queue[AST]()
    todo.push(ast)
    
     
    
    while (!todo.isEmpty) {
      val nextItem = todo.pop()
      (nextItem.symbol) match {
        
       case (RoundingModeEquality)| 
            (FPEqualityFactory(_)) |
            (FPFPEqualityFactory(_)) => {
            toEvaluateEquality += nextItem //reconstructSubtree(nextItem, decodedModel, candidateModel)
        }
        
       case fpPred : FloatingPointPredicateSymbol => {
         toReconstructPredicate += nextItem
       }
            
       case _ if nextItem.symbol.sort == BooleanSort => {
         toEvaluateBoolean.push(nextItem)
          for (c <- nextItem.children)
            todo.push(c)
        }
        
      }
    }
    
//    var eqDependency = new HashMap[AST, Set[ConcreteFunctionSymbol]] with MultiMap[AST, ConcreteFunctionSymbol]
//    
//
//    for ( eq <- toEvaluateEquality.toList) {
//      val lhsVars = eq.children(0).iterator.filter(_.isVariable)
//      val rhsVars = eq.children(1).iterator.filter(_.isVariable)
//      
//      if (eq.children(0).isVariable) {
//        for (v <- rhsVars)
//          eqDependency.addBinding(eq, v.symbol)
//      }
//
//      if (eq.children(1).isVariable) {
//        for (v <- lhsVars)
//          eqDependency.addBinding(eq, v.symbol)
//      }
//      
//      if (!eq.children(0).isVariable && !eq.children(1).isVariable) {
//        val variables = eq.children.map(_.iterator.filter(_.isVariable)).flatten
//        for (v <- variables)
//          eqDependency.addBinding(eq, v.symbol)      
//      }
//    }   
//          
//    for ( eq <- toEvaluateEquality.toList) {
//      val variables = eq.children.map(_.iterator.filter(_.isVariable)).flatten
//      for (v <- variables) {
//        eqDependency.addBinding(eq, v.symbol)
//      }
//    }
    
    var eqDependency = new HashMap[AST, Set[(Set[ConcreteFunctionSymbol], ConcreteFunctionSymbol)]] with MultiMap[AST, (Set[ConcreteFunctionSymbol], ConcreteFunctionSymbol)]
    
    import scala.collection.mutable.Set
    
    for ( eq <- toEvaluateEquality.toList) {
      val lhsVars = eq.children(0).iterator.filter(_.isVariable).map(_.symbol).toList
      val rhsVars = eq.children(1).iterator.filter(_.isVariable).map(_.symbol).toList
      
      if (lhsVars.size + rhsVars.size == 0)
        throw new Exception("No variables in equality?")
      
      val (lhs, rhs) = (eq.children(0), eq.children(1))
      val binding : List[ ( Set[ConcreteFunctionSymbol], ConcreteFunctionSymbol) ] =
        (lhs.isVariable, rhs.isVariable) match {
          case (true, true) => List( (Set(lhs.symbol), rhs.symbol), (Set(rhs.symbol), lhs.symbol) )
          case (true, false) => List( ( Set() ++ rhsVars.toSet, lhs.symbol) )
          case (false, true) => List( ( Set() ++ lhsVars.toSet, rhs.symbol) )
          case (false, false) => List( (Set() ++ (lhsVars ++ rhsVars).toSet, (lhsVars ++ rhsVars).toList.head) )
      }

      for (b <- binding)
        eqDependency.addBinding(eq, b)
    }


    
      
    val equalitySort = Toolbox.topologicalSortEqualities(eqDependency)

      
    val eqSet1 = toEvaluateEquality.toSet
    val eqSet2 = equalitySort.toSet
    
      
      
    println("non-sorted equalities:")
    for (eq <- eqSet1) 
      eq.prettyPrint("$")
    println("topological sorted equalities: ")
    for (eq <- eqSet2)
      eq.prettyPrint("£")
      println("end")
    
    equalitySort.map(reconstructSubtree(_, decodedModel, candidateModel))
    //toEvaluateEquality.map(reconstructSubtree(_, decodedModel, candidateModel))
    toReconstructPredicate.map(reconstructSubtree(_, decodedModel, candidateModel))
    toEvaluateBoolean.map(reconstructNode(decodedModel, candidateModel, _))
    candidateModel
    
  }  
}
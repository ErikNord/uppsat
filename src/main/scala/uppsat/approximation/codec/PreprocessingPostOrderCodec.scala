package uppsat.approximation.codec

import uppsat.ast.AST
import uppsat.ast.AST.Label

import uppsat.precision.PrecisionOrdering
import uppsat.precision.PrecisionMap
import uppsat.ModelEvaluator.Model
import uppsat.approximation._
import uppsat.ast.ConcreteFunctionSymbol

trait PreprocessingPostOrderCodec extends Codec {
  def encodeNode(symbol : ConcreteFunctionSymbol, label : Label, children : List[AST], precision : Precision) : AST 
  def decodeNode(args : (Model, PrecisionMap[Precision]), decodedModel : Model, ast : AST) : Model
  def preprocess(ast : AST) : Unit //Uses sideffects
  
  def encodeFormula(ast : AST, pmap : PrecisionMap[Precision]) : AST = {
    preprocess(ast)
    encodeSubFormula(ast, pmap)
    
  }

  def encodeSubFormula(ast : AST, pmap : PrecisionMap[Precision]) : AST = {
    val AST(symbol, label, children) = ast
    val newChildren =
      for (c <- children) yield {
        encodeSubFormula( c, pmap)
      }
    encodeNode(symbol, ast.label, newChildren, pmap(ast.label))
  }
  def decodeModel(ast : AST, appModel : Model, pmap : PrecisionMap[Precision]) : Model = {
    val decodedModel = new Model()
    AST.postVisit(ast, decodedModel, (appModel, pmap), decodeNode)
    decodedModel
  }
}


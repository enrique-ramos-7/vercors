package vct.col.rewrite

import vct.col.ast.{DerefPointer, DerefHeapVariable, HeapLocal, Expr, Star, Perm, And, PointerType, Type, TNonNullPointer, TNonNullConstPointer, BooleanValue}
import vct.col.rewrite.NonLatchingRewriter


case class CleanForPrinting[G]() extends NonLatchingRewriter[G,G] {
  override def dispatch(expr: Expr[G]): Expr[G] =
    expr match {
      case DerefPointer(h @ DerefHeapVariable(_)) => dispatch(h)
      case DerefPointer(h @ DerefHeapVariable(_)) => dispatch(h)
      case DerefPointer(h @ HeapLocal(_)) => dispatch(h)
      case Star(Perm(_,_),r) => dispatch(r)
      case Star(l,Perm(_,_)) => dispatch(l)
      case s @ Star(l,r) => 
        (dispatch(l), dispatch(r)) match {
        case (Perm(_,_), r) => r
        case (l,Perm(_,_)) => l
        case (l, r) => And(l,r)(s.o)
      }
      case p @ Perm(_,_) => new BooleanValue[G](true)(p.o) 
      case e => e.rewriteDefault()
    }

  override def dispatch(ttype: Type[G]): Type[G] = 
    ttype match {
      case p: TNonNullPointer[G] => dispatch(p.element)
      case p: TNonNullConstPointer[G] => dispatch(p.element)
      case e => e.rewriteDefault()
    }

}

/*
 * Copyright 2011 Thomas Sternagel.
 * GNU Lesser General Public License
 * This file is part of termlib.
 *
 * termlib is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * termlib is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied
 * warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
 * See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU
 * Lesser General Public License
 * along with termlib.  If not, see
 * <http://www.gnu.org/licenses/>.
 */

package term

package object indexing {
  import show._
  import scala.collection.immutable.HashMap
  import scala.collection.immutable.HashSet

  type IT = (Int,Term)
  type PString = List[((Term,Int),Term)]
  type Candis = HashSet[Int]
  type Trie = HashMap[Term,DT]

  case object EmptyFlatTerm extends Exception
  case object TermNotInIndex extends Exception
  case object RetrievalError extends Exception
  case class IllegalState(f:FT) extends Exception

  def wild = Var("^")

  object FT {
    def empty = new FT(Nil)
    def apply = empty
    private def ofPstring(p:PString):FT = {
      def _ofPstring(p:PString):(FT,List[FT]) = p match {
        case Nil => (empty,List(empty))
        case ((p1,ar),subterm)::tl => {
          val (FT(rl),ra) = _ofPstring(tl)
          val rap = ra.drop(ar)
          val after = rap.head
          val th = FT((p1,after,subterm)::rl)
          (th,th::rap)
        }
      }
      _ofPstring(p)._1
    }
    def ofTerm(t:Term) = {
      val vl = t.vars
      val rho = vl.foldRight(Subst())((v,s) => s + (v,wild))
      val twild = t(rho)
      val ps = twild.pstring
      ofPstring(ps)
    }
  }
  /**
    * A flatterm is a list of triples containing
    * - the root symbol of the current term,
    * - a reference to the "after"-term, and
    * - the whole current term */
  case class FT(ls:List[(Term,FT,Term)]) {
    def isEmpty = ls.isEmpty
    def root = ls match {
      case (r,_,_)::_ => Some(r)
      case _ => None
    }
    def next:FT = ls match {
      case _::l => FT(l)
      case  _ => throw EmptyFlatTerm 
    }
    def after:FT = ls match {
      case (_,a,_)::_ => a
      case _ => throw EmptyFlatTerm
    }
    def term = ls match {
      case (_,_,t)::_ => t
      case _ => throw EmptyFlatTerm
    }
    def arity:Int = ls match {
      case (_,_,t)::_ => if (t.isVar) 0 else t.args.length
      case _ => throw EmptyFlatTerm
    }
    def size = ls.length
    /*
    def toStringBuilder(implicit b:ImplicitBuilder):StringBuilder =
    ls match {
      case 
    }
    override def toString = toStringBuilder.result()
    */
  }
  trait TermIndex {
    def insert(t:IT):TermIndex
    def remove(t:IT):TermIndex
    def insert(ts:List[IT]):TermIndex
    def remove(ts:List[IT]):TermIndex
    def units(q:Term):Candis
    def insts(q:Term):Candis
    def gents(q:Term):Candis
    def varts(q:Term):Candis
  }

  object DT {
    def empty:DT = new Node(new Trie, new HashSet[DT])
    def init(ts:List[IT]) = ts.foldLeft(empty)((t,x) => t.insert(x))
  }
  sealed abstract class DT extends TermIndex {
    private var hash = 0
    override def hashCode() = {
      if (hash == 0) hash = super.hashCode() 
      hash
    }
    private def n[A] = (_:List[(A,A)]).head._2
    def insert(t:IT) = {
      def _insert(p:FT,trie:DT):List[(DT,DT)] = (p.root,trie) match {
        case (None,Leaf(set)) => List((trie,Leaf(set + t._1)))
        case (None,Node(_,_)) => List((trie,Leaf(new Candis + t._1)))
        case (Some(p1),Node(tn,jt)) => {
          val tp = if (tn.contains(p1)) tn(p1) else DT.empty
          val jtr = _insert(p.next,tp)
          val tnew = tn + (p1 -> n(jtr))
          val ar = p.arity
          val jtnew = if (jtr.length > ar) {
            val (jtrm,jtadd) = jtr(ar)
            (jt - jtrm) + jtadd
          } else {
            jt
          }
          val node = new Node(tnew,jtnew)
          val res = (trie,node)::(jtr.drop(ar))
          res
        }
        case _ => throw IllegalState(p)
      }
      val ft = FT.ofTerm(t._2)
      val ls = _insert(ft,this)
      n(ls)
    }
    def insert(ts:List[IT]) = ts.foldLeft(this)((t,x) => t.insert(x))
    def remove(t:IT) = {
      def _remove(p:FT,trie:DT):(List[(DT,DT)],Boolean) = (p.root,trie) match {
        case (None,Leaf(set)) => (List((trie,Leaf(set - t._1))),(set - t._1).isEmpty)
        case (Some(p1),Node(tn,jt)) => {
          if (tn.contains(p1)) {
            val (jtr,empty) = _remove(p.next,tn(p1))
            val ar = p.arity
            val (jtrm,jtadd) = jtr(ar)
            val jtnew = (jt - jtrm) + jtadd
            val tnew = if (empty) tn - p1 else tn + (p1 -> n(jtr))
            val node = new Node(tnew,jtnew)
            val jtnew2 = (trie,node)::(jtr.drop(ar))
            (jtnew2,tnew.isEmpty)
          } else {
            throw TermNotInIndex
          }
        }
        case _ => throw IllegalState(p)
      }
      val ft = FT.ofTerm(t._2)
      val (jt,_) = _remove(ft,this)
      n(jt)
    }
    def remove(ts:List[IT]) = ts.foldLeft(this)((t,x) => t.remove(x))
    def next(t:Term) = this match {
      case Node(nl,_) if (nl.contains(t)) => Some(nl(t))
      case _ => None
    }
    def skip = this match {
      case Node(_,jl) => jl.map(Some(_))
      case _ => new HashSet[Option[DT]]
    }
    private def retrieve(skipTerm:Boolean,skipTree:Boolean,t:Term) = {
      def retrieve(ft:FT,tree:Option[DT]):Candis = (tree,ft.root) match {
        case (None,_) => new Candis
        case (Some(Leaf(s)),None) => s
        case (Some(n @ Node(_,_)),Some(Var(_))) if (skipTree) => {
          val s = n.skip.map(retrieve(ft.next,_))
          s.foldRight(new Candis)(_ ++ _)
        }
        case (Some(n @ Node(_,_)),Some(Var(_))) => 
          retrieve(ft.next,n.next(wild))
        case (Some(n @ Node(_,_)),Some(fs @ Fun(_,_))) if (skipTerm) => {
          val s1 = retrieve(ft.next,n.next(fs))
          val s2 = retrieve(ft.after,n.next(wild))
          s1 ++ s2
        }
        case (Some(n @ Node(_,_)),Some(fs @ Fun(_,_))) =>
          retrieve(ft.next,n.next(fs))
        // term was not in the index
        case (Some(Leaf(_)),Some(_)) => { println("Some(Leaf),Some(_)");new Candis }
        // term ended befor we reached a Leaf ...
        case (Some(Node(_,_)),None) => { println("Some(Node(_)),None");new Candis }
        // this should now not be accessible anymore ...
        case c => throw RetrievalError
      }
      retrieve(FT.ofTerm(t),Some(this))
    }
    def units(t:Term) = retrieve(true,true,t)
    def insts(t:Term) = retrieve(false,true,t)
    def gents(t:Term) = retrieve(true,false,t)
    def varts(t:Term) = retrieve(false,false,t)
  }
  case class Leaf(cs:Candis) extends DT
  case class Node(ns:Trie,js:HashSet[DT]) extends DT
}

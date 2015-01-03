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

/** Provides functionality needed for lexicographic path ordering (LPO).
  *
  * ==Overview==
  * An LPO needs a precedence on function symbols which is provided by class
  * [[term.lpo.Precedence]]. */
package object lpo {
  import term._
  import term.util.{TRS,R}
  import term.Term.F
  import scala.util.parsing.combinator._
  import scala.language.postfixOps

  /** Represents a relation on function symbols. */
  type Rela = List[(F,F)]

  /** Represents a precedence on function symbols.
    * 
    * @param pairs the relation on function symbols used in ''this'' 
    * precedence */
  class Precedence(val pairs: Rela) {
    def this(elem: (F,F), pairs: Rela) = this(elem :: pairs)
    def this(l1: Rela, l2: Rela) = this(l1 ::: l2)
    /** Returns a list representation of ''this'' precedence. */
    def toList = pairs.distinct.sortWith(comp(_,_))
    /** Returns ''true'' if ''this'' precedence admits no infinite descending
      * sequences on function symbols and ''false'' otherwise. */
    def consistent = (pairs intersect pairs.map(_.swap)) == Nil
    /** Returns the reflexive and transitive closure of ''this'' precedence. */
    def star = {
      val sig = 
        pairs.flatMap(x => List(x._1,x._2)).distinct.sortWith(_ < _)
      val n = sig.length
      var a = Array.fill(n,n)(false)
      for ((f,i) <- sig.zipWithIndex)
        for ((g,j) <- sig.zipWithIndex)
          if (pairs contains (f,g)) a(i)(j) = true
      
      a = warshall(a, n)

      var res: Rela = Nil
      for ((f,i) <- sig.zipWithIndex)
        for ((g,j) <- sig.zipWithIndex)
          if (a(j)(i)) res = (g,f) :: res

      new Precedence(res.distinct.sortWith(comp(_,_)))
    }
    override def toString = {
      var str = ""
      if (!toList.isEmpty) {
        for (((g,f),i) <- toList.zipWithIndex) {
          str += g +" > "+ f
          if (i != toList.length-1) str += ", "
        }
      }
      str
    }
    private def warshall(x: Array[Array[Boolean]], n: Int) = {
      var a = x
      // Warshall Algorithm
      for (r <- 0 until n) {
        var tmp = a
        for (i <- 0 until n)
          for (j <- 0 until n)
            if (!a(i)(j) && a(i)(r) && a(r)(j)) tmp(i)(j) = true
        a = tmp
      }
      a
    }
    private def comp(t: (F,F), s: (F,F)): Boolean = {
      if (t._1 < s._1) true
      else
        if (t._1 == s._1 && t._2 < s._2) true
          else false
    }
    def min:F = {
      val ls = toList
      def aux(m:F,rs:Rela):F = rs match {
        case Nil => m
        case (g,f)::xs => if (g==m) aux(f,ls) else aux(m,xs)
      }
      aux(ls.head._2,ls)
    }
    def dropped(m:F):Precedence = new Precedence(toList.filter(t=>t._2==m))
    def linearize:List[(F,Int)] = {
      def aux(i:Int,missing:List[F],ps:Precedence):List[(F,Int)] = 
        ps.toList match {
        case Nil => missing.map(d=>(d,i))
        case ls => {
          val m = ps.min 
          val ds = ps.dropped(m)
          val mis = (ds.toList.map(_._1):::missing).distinct.filterNot(_==m)
          val rs = ls diff ds.toList
          (m,i)::aux(i+1,mis,new Precedence(rs))
        }
      }
      aux(0,Nil,this)
    }
  }

  /** A parser to parse a precedence from a string. */
  object PrecParser extends RegexParsers {
    private def fun: Parser[F] = """[a-zA-Z0-9_]\w*""".r
    private def pair: Parser[(F,F)] = fun~">"~fun ^^ { case f~_~g => (f,g) }
    private def rels: Parser[Rela] = repsep(pair, ",")
    /** Returns the precedence parsed from the string ''s''. */
    def parse(s: String): Precedence =
      new Precedence(parseAll(rels, s).getOrElse(Nil))
  }
  /*
  def lpo(s: Term, t: Term, p: Precedence): Boolean = 
    lpo3(s,t,p) || lpo1(s,t,p) || lpo2(s,t,p)
  private def lpo1(s: Term, t: Term, p: Precedence) =
    (!s.isVar && s.root == t.root && s.args.length == t.args.length) && 
    lpo1helper(s,t,p)
  private def lpo1helper(s: Term, t: Term, p: Precedence) = {
    val l = (s.args zip t.args).dropWhile(x => x._1 == x._2)
    lpo(l.head._1,l.head._2,p) &&
    l.tail.map(_._2).forall(x => lpo(s,x,p))
  }
  private def lpo2(s: Term, t: Term, p: Precedence) =
    !t.isVar && t.args.forall(x => lpo(s,x,p)) &&
    (
      p.pairs.contains((s.root.right.get,t.root.right.get)) ||
      new Precedence(
        (s.root.right.get,t.root.right.get)::p.pairs
      ).consistent ||
      new Precedence(
        (t.root.right.get,s.root.right.get)::p.pairs
      ).consistent
    )
  private def lpo2helper(s: Term, t: Term, p: Precedence) = {
    
  }
  private def lpo3(s: Term, t: Term, p: Precedence) =
    !s.isVar && s.args.exists(x => (lpo(x,t,p) || x == t))
  */
  /** Returns ''true'' if the term rewrite system ''trs'' can be shown
    * terminating using LPO and ''false'' otherwise. */
  def lpob(trs: TRS, p: Precedence) = lpo(trs,p)._1
  /** Returns the precedence on function symbols in ''trs'' which can show
    * ''trs'' terminating with lpo. */
  def lpop(trs: TRS, p: Precedence) = lpo(trs,p)._2
  def lpoX(trs: TRS, p: Precedence): (Boolean,Option[Precedence]) = {
    val ret = lpo(trs,p)
    (ret._1,Some(ret._2))
  }
  /** Returns the tuple (lpob,lpop). */
  def lpo(trs: TRS, p: Precedence): (Boolean,Precedence) = {
    var ret = (true,p)
    var p2 = p
    for (i <- trs.indices.toList) {
      val c = lpo((trs(i).lhs,trs(i).rhs),p2)
      if (ret._1)
        if (c._1) {
          ret = (true,c._2)
          p2 = c._2
        } else ret = (false,p)
    }
    ret
  }
  private def lpo(r: (Term,Term), p: Precedence): (Boolean,Precedence) = {
    if (Thread.currentThread.isInterrupted) throw new InterruptedException
    //lpo1(s,t,p) || lpo3(s,t,p) || lpo2(s,t,p)
    if (!r._1.isVar) {
      val (b1,p1) = lpo1(r,p)
      if (b1) (true,p1)
      else {
        val (b3,p3) = lpo3(r,p)
        if (b3) (true,p3)
        else {
          val (b2,p2) = lpo2(r,p)
          if (b2) (true,p2)
          else (false,p)
        }
      }
    } else (false,p)
  }
  private def lpo1(r: (Term,Term), p: Precedence) = 
    //(!s.isVar && s.root == t.root && s.args.length == t.args.length) && 
    //lpo1helper(s,t,p)
    if (/*!r._1.isVar && */
        r._1.root == r._2.root && 
        r._1.args.length == r._2.args.length)
      lpo1helper(r,p)
    else (false,p)
  private def lpo1helper(r: (Term,Term), p: Precedence) = {
    /*val l = (s.args zip t.args).dropWhile(x => x._1 == x._2)
    lpo(l.head._1,l.head._2,p) &&
    l.tail.map(_._2).forall(x => lpo(s,x,p))*/
    val l = (r._1.args zip r._2.args).dropWhile(x => x._1 == x._2)
    if (!l.isEmpty) {
      val (b1,p1) = lpo((l.head._1,l.head._2),p)
      val lt = l.tail.map(_._2)
      var ret = (true,p)
      var p2 = p
      for (i <- lt.indices.toList) {
        val c = lpo((r._1,lt(i)),p2)
        if (ret._1)
          if (c._1) {
            ret = (true,c._2)
            p2 = c._2
          } else ret = (false,p)
      }
      if (b1 && ret._1) {
        //(b1 && ret._1, new Precedence((p1.pairs:::ret._2.pairs) distinct))
        val p3 = new Precedence((p1.pairs:::ret._2.pairs) distinct)
        if (p3.star.consistent) (true,p3)
        else (false,p)
      } else (false,p)
    } else (false,p)
  }
  private def lpo2(r: (Term,Term), p: Precedence) = {
    /*!t.isVar && t.args.forall(x => lpo(s,x,p)) &&
    (
      p.pairs.contains((s.root.right.get,t.root.right.get)) ||
      new Precedence(
        (s.root.right.get,t.root.right.get)::p.pairs
      ).star.consistent ||
      new Precedence(
        (t.root.right.get,s.root.right.get)::p.pairs
      ).star.consistent
    )*/
    if (!r._2.isVar) {
      var ret = (true,p)
      var p2 = p
      for (i <- r._2.args.indices.toList) {
        val c = lpo((r._1,r._2.args(i)),p2)
        if (ret._1)
          if (c._1) {
           ret = (true,c._2)
           p2 = c._2
          } else ret = (false,p)
      }
      if (ret._1) lpo2helper(r,ret._2)
      else (false,p)
    } else (false,p)
  }
  private def lpo2helper(r: (Term,Term), p: Precedence) = {
    val (s,t) = (r._1.root.right.get,r._2.root.right.get)
    if (p.pairs.contains((s,t))) {
      (true,p)
    } else {
      val p1 = new Precedence(
        ((s,t)::p.pairs) distinct
      )
      if (p1.star.consistent) (true,p1)
      //else {
        //val p1 = new Precedence(
          //((t.root.right.get,s.root.right.get)::p.pairs) distinct
        //)
        //if (p1.star.consistent) (true,p1)
        else (false,p)
      //}
    }
  }
  private def lpo3(r: (Term,Term), p: Precedence) =
    //!s.isVar && s.args.exists(x => (lpo(x,t,p) || x == t))
    /*if (!r._1.isVar)*/ {
      var ret = (false,p)
      for (i <- r._1.args.indices.toList) {
        val c = lpo((r._1.args(i),r._2),p)
        if (!ret._1)
          if (r._1.args(i) == r._2) {
            ret = (true,p)
          } else if (c._1) {
            ret = (true,c._2)
          }
      }
      ret
    } /*else (false,p)*/
}


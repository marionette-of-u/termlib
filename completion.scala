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

/** Provides functions needed for a completion procedure.
  * 
  * Such a procedure takes as input a set of equations ''E'' and a termination 
  * method and attempts to cunstruct a terminating and confluent, i.e. complete,
  * term rewrite system ''R'' which has the same set of convertible terms as
  * ''E''.
  *
  * Completion is implemented as an inference system. The rules of which operate
  * on a triple ''(E,R,C)'' and return a new triple ''(E',R',C')''. Here ''E''
  * is a set of equations, ''R'' a set of rewrite rules, and ''C'' a constraint
  * term rewrite system used to allow other termination methods besides
  * reduction orderings. */
package object completion {
  import term._
  import util._
  import lpo._
  import parser._
  import java.io._
  import java.util.concurrent._
  import scala.language.postfixOps

  /** A termination method (TM) is a function which yields ''true'' if a given
    * term rewrite system terminates and ''false'' otherwise. */
  type TM = TRS => (Boolean,Option[Precedence])

  /** Only added to generate scaladoc for [[term.completion]] correctly :( */
  object Completion {}
  /** Returns the triple ''(E',R',C')'' where equations in ''E'' with indices in 
    * ''is'' are oriented from left to right into rewrite rules and moved to
    * ''R'' using the termination method ''tm'' and the unchanged triple
    * ''(E,R,C)'' if not all equations with indices in ''is'' could be oriented 
    * from left to right using ''tm''.
    * 
    * @param is a list of indices in ''E'' 
    * @param erc a triple ''(E,R,C)'' where ''E'' is an equational system, ''R''
    * is a term rewrite system, and ''C'' is a constraint term rewrite system 
    * @param tm the used termination method */
  def orientLR(is: List[Int], erc: ERC, tm: TM): (ERC,Option[Precedence]) = 
    orient(is,erc,tm,true)
  /** Returns the triple ''(E',R',C')'' where equations in ''E'' with indices in 
    * ''is'' are oriented from right to left into rewrite rules and moved to
    * ''R'' using the termination method ''tm'' and the unchanged triple
    * ''(E,R,C)'' if not all equations with indices in ''is'' could be oriented 
    * from right to left using ''tm''.
    * 
    * @param is a list of indices in ''E'' 
    * @param erc a triple ''(E,R,C)'' where ''E'' is an equational system, ''R''
    * is a term rewrite system, and ''C'' is a constraint term rewrite system 
    * @param tm the used termination method */
  def orientRL(is: List[Int], erc: ERC, tm: TM): (ERC,Option[Precedence]) = 
    orient(is,erc,tm,false)
  /** Returns the result from ''orientLR'' if it changed the triple ''(E,R,C)''
    * and the result from ''orientRL'' otherwise. 
    * 
    * @param is a list of indices in ''E'' 
    * @param erc a triple ''(E,R,C)'' where ''E'' is an equational system, ''R''
    * is a term rewrite system, and ''C'' is a constraint term rewrite system 
    * @param tm the used termination method */
  def orient(is: List[Int], erc: ERC, tm: TM): (ERC,Option[Precedence]) = {
    val (next,p) = orientLR(is,erc,tm)
    if (next != erc) (next,p) else orientRL(is,erc,tm)
  }
  private def orient(is: List[Int], erc: ERC, tm: TM, lr: Boolean):
  (ERC,Option[Precedence]) = {
    val (in,out) = partition(is, erc._1)
    val ts = if (lr) in.map(_.toRule) else in.map(_.swap.toRule)
    val (t,p) = tm(ts:::erc._3)
    if (t)
     ((out, (erc._2:::ts) distinct,(erc._3:::ts) distinct),p)
    else ((combine(is,in,out),erc._2,erc._3),None)
  }
  /** Returns ''(E',R,C)'' where all trivial equations from ''E'' with indices
    * in ''is'' are removed from ''E''.
    * 
    * A trivial equation is an equation where the left-hand side is the same as
    * the right-hand side.
    *
    * @param is a list of indices in ''E'' 
    * @param erc a triple ''(E,R,C)'' where ''E'' is an equational system, ''R''
    * is a term rewrite system, and ''C'' is a constraint term rewrite system */
  def delete(is: List[Int], erc: ERC): ERC = {
    val (in,out) = partition(is, erc._1)
    val rest = in.filterNot(x => x.lhs == x.rhs)
    (combine(is, rest, out) distinct, erc._2, erc._3)
  }
  /** Returns ''(E',R,C)'' where all left- and right-hand sides of equations
    * from ''E'' with indices in ''is'' are reduced one step with respect to 
    * ''R''.
    *
    * @param is a list of indices in ''E'' 
    * @param erc a triple ''(E,R,C)'' where ''E'' is an equational system, ''R''
    * is a term rewrite system, and ''C'' is a constraint term rewrite system */
  def simplify(is: List[Int], erc: ERC): ERC = {
    val (in,out) = partition(is, erc._1)
    (combine(is,in.map(_.simpl(erc._2)),out) distinct, 
      erc._2,erc._3)
  }
  /** Returns ''(E',R,C)'' where all left- and right-hand sides of equations
    * from ''E'' with indices in ''is'' are reduced to normal form with respect 
    * to ''R''.
    *
    * @param is a list of indices in ''E'' 
    * @param erc a triple ''(E,R,C)'' where ''E'' is an equational system, ''R''
    * is a term rewrite system, and ''C'' is a constraint term rewrite system */
  def simplifyToNF(is: List[Int], erc: ERC): ERC = {
    val (in,out) = partition(is, erc._1)
    (combine(is,in.map(_.simplToNF(erc._2)),out) distinct, 
      erc._2,erc._3)
  }
  /** Returns ''(E,R',C)'' where all right-hand sides of rules from ''R'' with 
    * indices in ''is'' are reduced one step with respect to ''R'' without the
    * reduced rule itself.
    *
    * @param is a list of indices in ''R'' 
    * @param erc a triple ''(E,R,C)'' where ''E'' is an equational system, ''R''
    * is a term rewrite system, and ''C'' is a constraint term rewrite system */
  def compose(is: List[Int], erc: ERC): ERC = {
    val (in,out) = partition(is, erc._2)
    (erc._1, combine(is,in.map(_.xReduceRHS(erc._2)),out)
      distinct, erc._3)
  }
  /** Returns ''(E,R',C)'' where all right-hand sides of rules from ''R'' with 
    * indices in ''is'' are reduced to normal form with respect to ''R'' 
    * without the reduced rule itself.
    *
    * @param is a list of indices in ''R'' 
    * @param erc a triple ''(E,R,C)'' where ''E'' is an equational system, ''R''
    * is a term rewrite system, and ''C'' is a constraint term rewrite system */
  def composeToNF(is: List[Int], erc: ERC): ERC = {
    val (in,out) = partition(is, erc._2)
    (erc._1, combine(is,in.map(_.xRewriteRHS(erc._2)),out)
      distinct, erc._3)
  }
  /** Returns ''(E',R',C)'' where all left-hand sides of rules from ''R'' with 
    * indices in ''is'' are reduced one step with respect to ''R'' without the
    * collapsed rule itself and then moved to ''E''.
    *
    * @param is a list of indices in ''R'' 
    * @param erc a triple ''(E,R,C)'' where ''E'' is an equational system, ''R''
    * is a term rewrite system, and ''C'' is a constraint term rewrite system */
  def collapse(is: List[Int], erc: ERC): ERC = {
    def aux(r: R, rs: TRS) = r.toEquation.xReduceLHS(rs)
    val (in,out) = partition(is, erc._2)
    val (yes,no) = in.partition(
    	rule => erc._2.exists(rule.xReduce(_).isDefined))
    val yese = yes.map(aux(_,erc._2))
    (erc._1:::yese distinct, combine(is,no,out), erc._3)    
  }
  /** Returns ''(E',R',C)'' where all left-hand sides of rules from ''R'' with 
    * indices in ''is'' are reduced to normal form with respect to ''R'' without
    * the collapsed rule itself and then moved to ''E''.
    *
    * @param is a list of indices in ''R'' 
    * @param erc a triple ''(E,R,C)'' where ''E'' is an equational system, ''R''
    * is a term rewrite system, and ''C'' is a constraint term rewrite system */
  def collapseToNF(is: List[Int], erc: ERC): ERC = {
    def aux(r: R, rs: TRS) = r.toEquation.xRewriteLHS(rs)
    val (in,out) = partition(is, erc._2)
    val (yes,no) = in.partition(
    	rule => erc._2.exists(rule.xReduce(_).isDefined))
    val yese = yes.map(aux(_,erc._2))
    (erc._1:::yese distinct, combine(is,no,out), erc._3)    
  }
  /** Returns ''(E',R,C)'' where all critical pairs between left-hand sides of
    * rules from ''R'' with indices in ''is'' are added to ''E''.
    *
    *
    * @param is a list of indices in ''R'' 
    * @param erc a triple ''(E,R,C)'' where ''E'' is an equational system, ''R''
    * is a term rewrite system, and ''C'' is a constraint term rewrite system */
  def deduce(is: List[Int], erc: ERC): ERC = {
    val (in,out) = partition(is, erc._2)
    (erc._1 union cps(in), erc._2, erc._3)
  }
  /** Returns ''(E',R,C)'' where all critical pairs between the left-hand side of
    * the rule from ''R'' with index ''i'' and all left-hand sides of rules in
    * ''R'' are added to ''E''.
    *
    * @param i an index in ''R'' 
    * @param erc a triple ''(E,R,C)'' where ''E'' is an equational system, ''R''
    * is a term rewrite system, and ''C'' is a constraint term rewrite system */
  def deduceS(i: Int, erc: ERC): ERC = {
    val (in,out) = partition(List(i), erc._2)
    ((erc._1 union cps(out, in) union cps(in, out) union cps(in, in) distinct), 
      erc._2, erc._3)
  }
  /** Returns ''(E',R,C)'' where all critical pairs between the left-hand side of
    * the rule from ''R'' with index ''i'' and all left-hand sides of rules in
    * ''R'' are added to ''E''.
    *
    * @param i an index in ''R'' 
    * @param erc a triple ''(E,R,C)'' where ''E'' is an equational system, ''R''
    * is a term rewrite system, and ''C'' is a constraint term rewrite system */
  def deduceE(i: Int, erc: ERC): ERC = {
    val (in,out) = partition(List(i), erc._2)
    ((erc._1 union cps(erc._2, in) union cps(in, erc._2) union cps(in,in)) 
      distinct, 
      erc._2, erc._3)
  }
  /** Returns ''true'' if ''rs'' is complete and has the same conversion as
    * ''es'' and ''false otherwise.  */
  def isComplete(es: ES, rs: TRS): Boolean =
    es.isEmpty && !rs.isEmpty && allCPsAreJoinable(es,rs)
  private def allCPsAreJoinable(es: ES, rs: TRS): Boolean = {
    val (cp,_,_) = deduce(rs.indices.toList, (es,rs,List[R]()))
    cp.forall(_.isJoinable(rs))
  }
  /*
  private def allCPsAreJoinable(es: ES, rs: TRS): Boolean = {
    class Worker(cps: ES) extends Callable[Boolean] {
      override def call:Boolean = {
        cps.forall(_.isJoinable(rs))
      }
    }
    val (cp,_,_) = deduce(rs.indices.toList, (es,rs,List[R]()))
    val t = 4
    val n = 100
    val exec: ExecutorService = Executors.newFixedThreadPool(t)
    val cs = new ExecutorCompletionService[Boolean](exec)
    val i = cp.grouped(cp.size/(n-1))
    val workers = (for (l <- i) yield new Worker(l)).toList
    //val workers = (for (i <- (0 until n).toList) yield 
    //  new Worker(cp.zipWithIndex.filter(_._2 % n == i).map(t => t._1))).toList
    val fs = workers.map(cs.submit(_))
    // block until all results are there
    val results = fs.map(_.get)
    results.forall(_ == true)
  }
  */
}

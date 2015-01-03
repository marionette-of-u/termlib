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

/** Contains some useful functionality to work with terms.
  *
  * ==Overview==
  * The class [[term.util.package.Equation]] for equation on terms is provided
  * as well as the class [[term.util.package.Rule]] for term rewrite rules. 
  * The object [[term.util.package.E]] is a factory for equations and 
  * [[term.util.package.R]] a factory for rules. The object 
  * [[term.util.package.MathSymbol]] provides some mathematical
  * unicode symbols. */
package object util {
  import term._
  import Term._
  import util._
  import reco._
  import show._
  import poly.Interpretation
  import scala.collection.immutable.HashMap
  import scala.language.implicitConversions
  import scala.language.postfixOps

  type CM = Option[(Interpretation,HashMap[String,String])]
  type SIG = List[Fun]


  class RichList[A](xs : List[A]) {
    /** Return f(x) for the first element x, where the result of f(x)
      * is unequal to None together with the index of x. */
    def indexOption[B](f : (A) => Option[B]) : Option[(Int, B)] = {
      var i = 0
      xs foreach { x =>
        f(x) match {
          case Some(y) => return Some(i, y)
          case None =>
        }
        i = i + 1
      }
      return None
    }

    def zipWith[B, C](ys : List[B])(f : (A, B) => C) : List[C] = (xs, ys) match {
      case (x::xs, y::ys) => f(x, y) :: xs.zipWith(ys)(f)
      case _ => Nil
    }

    def foldLeftIndex[B](z : B)(f : (Int, B, A) => B) : B =
      xs.foldLeft((z, 0))((zi, x) => (f(zi._2, zi._1, x), zi._2 + 1))._1

    def foldRightIndex[B](z : B)(f : (Int, A, B) => B) : B =
      xs.foldRight((z, xs.length - 1))((x, zi) => (f(zi._2, x, zi._1), zi._2 - 1))._1
  }
  implicit def list2RichtList[A](x : List[A]) : RichList[A] = new RichList(x)

  sealed abstract class TermPair(val lhs:Term,val rhs:Term) {
    private val tuple = (lhs,rhs)
    def toTuple = tuple
    def addVars(xs : Set[V]) = rhs.addVars(lhs.addVars(xs))
    /** Returns the Set of variables occuring in ''this'' pair of terms. */
    def vars = addVars(Set())
    def toXML : scala.xml.Elem =
      <rule><lhs>{lhs.toXML}</lhs><rhs>{rhs.toXML}</rhs></rule>
    def size:Int = lhs.size + rhs.size
  }

  /** Factory for [[term.util.package.Equation]] instances. */
  object Equation {
    implicit def tuple2ToEquation(t : Tuple2[Term, Term]) = Equation(t._1, t._2)
  }

  /** Represents an equation between two terms. 
    *
    * Equations are undirected so ''s'' \u2248 ''t'' is identified with ''t''
    * \u2248 ''s''. 
    * 
    * @constructor Creates a new equation from two terms.
    * @param lhs the left-hand side of the equation
    * @param rhs the right-hand side of the equation */
  case class Equation(override val lhs : Term, override val rhs : Term) extends TermPair(lhs,rhs) {
    private val tuple = (lhs, rhs)
    //def toTuple = tuple
    /** Returns ''this'' equation with swapped left- and right-hand sides. */
    def swap = Equation(rhs, lhs)
    def toRule : Rule = Rule(lhs, rhs)
    def apply(s: Subst) : Equation = Equation(lhs(s), rhs(s))
    // the hash code must be equal for all equations that are considered equal
    // by method 'equals'
    override def hashCode = tuple.hashCode + tuple.swap.hashCode
    override def equals(other : Any) : Boolean = other match {
      case that : Equation =>
        that.canEqual(this) &&
          tuple.equals(that.toTuple) || tuple.equals(that.toTuple.swap)
      case _ => false
    }
    def canEqual(that : Any) : Boolean = that.isInstanceOf[Equation]
    def toStringBuilder(implicit b : ImplicitBuilder) = {
      val lhsBuilder = lhs.toStringBuilder(b)
      rhs.toStringBuilder(lhsBuilder.append(" ").
        append(MathSymbol.AlmostEqualTo).append(" "))
      //lhs.toStringBuilder(b).append(" ").append(MathSymbol.AlmostEqualTo).
      //  append(" ").append(rhs.toStringBuilder(b))
    }
    override def toString() = toStringBuilder.result()
    /** Returns ''this'' equation with the left-hand side reduced by one step
      * with respect to the term rewrite system ''rs''. */
    def simplLHS(rs: TRS): E = E(lhs.rewriteStep(rs).getOrElse(lhs), rhs)
    /** Returns ''this'' equation with the left-hand side reduced by one step
      * with respect to the indexed term rewrite system ''irs''and the index
      * of the used rule from ''irs''. */
    def simplLHS(irs: List[IR]): (E,Int) = {
      val (i,l) = lhs.irewriteStep(irs).getOrElse((-1,lhs))
      (E(l,rhs),i)
    }
    def simplRHS(irs: List[IR]): (E,Int) = {
      val (i,r) = rhs.irewriteStep(irs).getOrElse((-1,rhs))
      (E(lhs,r),i)
    }
    /** Returns ''this'' equation with the left-hand side reduced to normal form
      *with respect to the term rewrite system ''rs''. */
    def simplLHSToNF(rs: TRS): E = E(lhs.rewrite(rs), rhs)
    /** Returns ''this'' equation with the right-hand side reduced by one step
      * with respect to the term rewrite system ''rs''. */
    def simplRHS(rs: TRS): E = E(lhs, rhs.rewriteStep(rs).getOrElse(rhs))
    /** Returns ''this'' equation with the right-hand side reduced to normal
      * form with respect to the term rewrite system ''rs''. */
    def simplRHSToNF(rs: TRS): E = E(lhs, rhs.rewrite(rs))
    /** Returns ''this'' equation with the left- and right-hand sides reduced by
      * one step with respect to the term rewrite system ''rs''. */
    def simpl(rs: TRS): E = simplLHS(rs).simplRHS(rs)
    /** Returns ''this'' equation with the left- and right-hand sides reduced to
      * normal form with respect to the term rewrite system ''rs''. */
    def simplToNF(rs: TRS): E = simplLHSToNF(rs).simplRHSToNF(rs)
    /** Returns ''this'' equation with the left-hand side reduced by one step 
      * with respect to ''rs'' without any rules equal to ''this'' equation. */
    def xReduceLHS(rs: TRS): E = simplLHS(rs.filterNot(_ == toRule))
    def xReduceLHS(irs: List[IR]): (E,Int) =
      simplLHS(irs.filterNot(_._2 == toRule))
    /** Returns ''this'' equation with the left-hand side reduced to normal form 
      * with respect to ''rs'' without any rules equal to ''this'' equation. */
    def xRewriteLHS(rs: TRS): E = simplLHSToNF(rs.filterNot(_ == toRule))
    /** Returns ''true'' if ''this'' equation is a trivial equation, i.e., the
      * left- and right-hand sides of ''this'' equations are the same, and
      * ''false'' otherwise. */
    def isTrivial: Boolean = lhs == rhs
    /** Returns ''true'' if the left- and right-hand sides of ''this'' equation
      * may be rewritten to the same normal form with respect to ''rs''. */
    def isJoinable(rs: TRS): Boolean = lhs.rewrite(rs) == rhs.rewrite(rs)
    /** Returns a list of all variables occuring in ''this'' equation. */
    //def addVars(xs : Set[V]) = rhs.addVars(lhs.addVars(xs))
    //def vars = addVars(Set())
    def addFunAris(fs : Set[(F,Int)]) = rhs.addFunAris(lhs.addFunAris(fs))
    def funAris = addFunAris(Set())
    //def toXML : scala.xml.Elem =
    //  <rule><lhs>{lhs.toXML}</lhs><rhs>{rhs.toXML}</rhs></rule>
    def joinable(itrs: ITRS): Boolean = {
      val sjs = lhs.rewriteToNF(itrs)
      val tjs = rhs.rewriteToNF(itrs)
      val snf = if (!sjs.isEmpty) sjs.reverse.head._3 else lhs 
      val tnf = if (!tjs.isEmpty) tjs.reverse.head._3 else rhs
      snf==tnf
    }
  }


  object Rule {
    implicit def tuple2Rule(t : Tuple2[Term, Term]) = Rule(t._1, t._2)
  }
  /** Represents a term rewrite rule.
    *
    * A term rewrite rule is a pair of terms where the restriction is that the
    * left-hand side may not be a variable and all the variables of the
    * right-hand side have to be contained in the left-hand side.
    * 
    * @constructor Creates a new rule from two terms.
    * @param lhs the left-hand side of the rule
    * @param rhs the right-hand side of the rule */
  case class Rule(override val lhs : Term, override val rhs : Term) extends TermPair(lhs,rhs) {
    require(!lhs.isVar,
      "variable left-hand side not allowed")
    require(rhs.vars.subsetOf(lhs.vars),
      "free variables in right-hand sides not allowed")

    //def toTuple = (lhs, rhs)
    def toEquation = Equation(lhs, rhs)

    /** Returns ''this'' rule after the substitution ''s'' was applied to the
      * left- and right-hand sides. */
    def apply(s: Subst): Rule = Rule(lhs(s), rhs(s))
    override def hashCode = (lhs, rhs).hashCode
    override def equals(other: Any): Boolean = other match {
      case that: Rule => (that canEqual this) && (lhs == that.lhs) && (rhs == that.rhs)
      case _ => false
    }
    override def canEqual(other: Any): Boolean = other.isInstanceOf[Rule]
    def toStringBuilder(implicit b : ImplicitBuilder) = {
      val lhsBuilder = lhs.toStringBuilder(b)
      rhs.toStringBuilder(lhsBuilder.append(" ").
        append(MathSymbol.RightArrow).append(" "))
      //lhs.toStringBuilder(b).append(" ").append(MathSymbol.RightArrow).
      //append(" ").append(rhs.toStringBuilder(b))
    }
    override def toString() = toStringBuilder.result()
    /** Returns ''true'' if the left-hand and right-hand sides of ''this'' rule
      * are variants of the left- and right-hand sides of ''that'' rule and
      * ''false'' otherwise. */
    def variantOf(that: Rule): Boolean = {
      if ((lhs matches that.lhs) && (rhs matches that.rhs)) {
        val s1 = lhs mmatch that.lhs
        val s2 = rhs mmatch that.rhs
        s2.subsetOf(s1) && s1.isRenaming
      } else false
    }
    /** Returns a list of overlaps between the left-hand sides of ''this'' rule
      * and rule ''r''. */
    def overlaps(r: Rule): List[Overlap] = {
      val rn1 = lhs.freshVars
      val r1 = this(rn1)
      val rn2 = r.lhs.freshVars
      val r2 = r(rn2)
      (for (
        p <- r1.lhs.possf 
        if r1.lhs(p) unifiable r2.lhs;
        if r1.check(p,r2)
      ) yield (this,p,r)).toList
    }
    def check(p: Pos, r: Rule): Boolean =
      p != Pos() || !variantOf(r)
    /** Returns a list of overlaps between the left-hand side of ''this'' rule
      * and the left-hand sides of rules from the term rewrite system 
      * ''trs''. */
    def overlaps(trs: TRS): List[Overlap] = 
    trs match {
      case Nil => List[Overlap]()
      case r :: rs => overlaps(r) ::: overlaps(rs)
    }
    /** Returns ''this'' rule after the left-hand side of it was rewritten one
      * time with respect to the term rewrite system ''rs''. */
    def simplLHS(rs: TRS): R = 
      R(lhs.rewriteStep(rs).getOrElse(lhs), rhs)
    /** Returns ''this'' rule after the right-hand side of it was rewritten one
      * time with respect to the term rewrite system ''rs''. */
    def simplRHS(rs: TRS): R = 
      R(lhs, rhs.rewriteStep(rs).getOrElse(rhs))
    def simplRHS(irs: List[IR]): (R,Int) = {
      val (i,r) = rhs.irewriteStep(irs).getOrElse((-1,rhs))
      (R(lhs,r),i)
    }
    /** Returns ''this'' rule after the right-hand side of it was rewritten to
      * normal form with respect to the term rewrite system ''rs''. */
    def simplRHSToNF(rs: TRS): R = R(lhs, rhs.rewrite(rs))
    /** Returns ''this'' rule after the left- and right-hand sides of it were
      * rewritten one time with respect to the term rewrite system ''rs''. */
    def simpl(rs: TRS): R = simplLHS(rs).simplRHS(rs)
    /** Returns ''this'' rule where the right-hand side is reduced by one step
      * with respect to ''rs'' without ''this'' rule itself. */
    def xReduceRHS(rs: TRS): R = simplRHS(rs.filterNot(_ == this))
    def xReduceRHS(irs: List[IR]): (R,Int) = simplRHS(irs.filterNot(_._2 == this))
    /** Returns ''this'' rule where the right-hand side is reduced to normal form
      * with respect to ''rs'' without ''this'' rule itself. */
    def xRewriteRHS(rs: TRS): R = simplRHSToNF(rs.filterNot(_ == this))
    /** Returns ''true'' if the left-hand side of ''this'' rule is reducible by
      * some rule from ''rs'' which is not equal to ''this'' rule. */
    def xReducibleLHS(rs: TRS): Boolean = 
      lhs.isReducible(rs.filterNot(_ == this))
    /** Returns ''[[scala.Some]](this)'' rule where the left-hand side is 
      * reduced by one step with respect to rule ''r'' if the left-hand side 
      * of ''r'' cannot be reduced by ''this'' rule and [[scala.None]] 
      * otherwise. */
    def xReduce(r: R): Option[Term] = {
      if (r.lhs.isReducible(List(this))) None
      else lhs.rewriteStep(List(r))
    }
    //def addVars(xs : Set[V]) = rhs.addVars(lhs.addVars(xs))
    /** Returns the Set of variables occuring in ''this'' rule. */
    //def vars = addVars(Set())
    //def toXML : scala.xml.Elem =
    //  <rule><lhs>{lhs.toXML}</lhs><rhs>{rhs.toXML}</rhs></rule>
  }

  /** This object provides meaningfull names for some usefull mathematical
   * unicode symbols. */
  object MathSymbol {
    /** The almost-euqal symbol: \u2248 */
    val AlmostEqualTo = '\u2248'
    /** The right-arrow symbol: \u2192 */
    val RightArrow = '\u2192'
    /** The left-arrow symbol: \u2190 */
    val LeftArrow = '\u2190'
    /** The empty-set symbol: \u2205 */
    val EmptySet = '\u2205'
    /** The epsilon symbol: \u03b5 */
    val Epsilon = '\u03b5'
    /** The times symbol: \u00d7 */
    val Times = '\u00d7'
    /** A vertical bar: \u007c */
    val VBar = '\u007c'
  }
  
  /** Returns ''true'' if termlib is running on a Microsoft Windows and
    * ''false'' otherwise. */
  def ms = 
    System.getProperty("os.name").contains("Microsoft") ||
    System.getProperty("os.name").contains("Windows")
  
  /** A tripel consisting of an equational system, a term rewrite system, and an
    * additional constraining term rewrite system.
    *
    * These tripels are used for completion runs which use external termination
    * tools. */
  type ERC = (ES,TRS,TRS)
  /** Shorthand for an [[term.util.package.Equation]]. */
  type E = Equation
  /** Factory for [[term.util.package.Equation]] instances. */
  object E {
    /** Creates an equation with left-hand side ''l'' and right-hand side
      * ''r''. */
    def apply(l: Term, r: Term) = Equation(l,r)

    /** Called in a pattern match { case E(...) }. */
    def unapply(e: Equation): Option[(Term,Term)] = Some((e.lhs,e.rhs))
  }
  /** Shorthand for a [[term.util.package.Rule]]. */
  type R = Rule
  /** Factory for [[term.util.package.Rule]] instances. */
  object R {
    /** Creates a rule with left-hand side ''l'' and right-hand side
      * ''r''. */
    def apply(l: Term, r: Term) = Rule(l,r)
    /** Called in a pattern match { case R(...) }. */
    def unapply(r: Rule): Option[(Term,Term)] = Some((r.lhs,r.rhs))
  }
  type S = List[TermPair]
  /** A term rewrite system (TRS) is a list of term rewrite rules. */
  type TRS = List[R]
  /** An equational system (ES) is a list of equations between terms. */
  type ES = List[E]
  /** An overlap is a tripel consisting of a term rewrite rule, a position, and
    * another term rewrite rule.
    *
    * The position shows where the left-hand side of the second rule overlaps
    * with the left-hand side of the first rule. */
  type Overlap = (Rule,Pos,Rule)

  def addVars(es:S,xs:Set[V]):Set[V] = es.foldLeft(xs)((xs, e) => e.addVars(xs))
  /** Returns the set of all variables used in the equational system ''es''. */
  def vars(es:S):Set[V] = addVars(es,Set[String]())
  def addVars(ies:IS,xs:Set[V]):Set[V] = addVars(ies.values.toList, xs)
  def vars(ies:IS):Set[V] = addVars(ies, Set[String]())
  def addFunAris(es:ES,fs:Set[(V,Int)]):Set[(V,Int)] =
    es.foldLeft(fs)((fs, e) => e.addFunAris(fs))
  def funAris(es:ES):Set[(F,Int)] = addFunAris(es,Set[(F,Int)]())
  /** Returns a list of all overlaps between left-hand sides of rules from the
    * term rewrite system ''trs''. */
  def overlaps(trs: TRS): List[Overlap] = {
    def aux(trs1: TRS): List[Overlap] = trs1 match {
      case Nil => List[Overlap]()
      case r :: rs => r.overlaps(trs) ::: aux(rs)
    }
    aux(trs)
  }
  /** Returns a list of all overlaps between left-hand sides of rules from
    * ''trs1'' and left-hand sides of rules from ''trs2''. */
  def overlaps(trs1: TRS, trs2: TRS): List[Overlap] = {
    def aux(trs1: TRS): List[Overlap] = trs1 match {
      case Nil => List[Overlap]()
      case r :: rs => r.overlaps(trs2) ::: aux(rs)
    }
    aux(trs1)
  }
  /** Returns the critical pair generated by the overlap ''ol''. */
  def crit_pair(ol: Overlap): E = {
    val (e1,p,e2) = ol
    val (l1n,r1n) = (e1.lhs, e1.rhs)
    val rn2 = e2.lhs.freshVars
    val (l2n,r2n) = (e2.lhs(rn2), e2.rhs(rn2))
    val sub = l1n(p) unify l2n
    // vars which are already there
    val vars1 = l1n.vars -- l1n(p).vars
    // vars which are to be renamed in a sane way
    val vars2 = l1n(sub)(p).vars ++ r2n(sub).vars
    // sane renaming
    val ren = saneVars(vars1, vars2)
    Equation(
      (l1n(sub)(p) = r2n(sub))(ren), 
      r1n(sub)(ren)
    ) 
  }
  private def nextVar(excl: Set[String]): String = {
    val names = Map(0->"x",1->"y",2->"z")
    var j = 0
    var i = -1
    def name = names(j) + (if (i <= 0) "" else i.toString)
    while (excl.contains(name)) {
      j = (j+1) % 3
      if (j == 0) i = i + 1
    }
    name
  }
  def saneVars(excl: Set[String], vs: Set[String]): Subst = {
    var i = 0
    var e = excl
    var s = Subst()
    var v = ""
    val vss = vs.toList
    while (i < vss.length) {
      v = nextVar(e)
      s = s + ((vss(i),Var(v)))
      e = e + v
      i = i + 1
    }
    s
  }
  /** Returns a list of critical pairs between left-hand sides of rules in
    * ''trs''. */
  def cps(trs: TRS): ES = {
    overlaps(trs) map (crit_pair(_)) distinct
  }
  /** Returns a list of critical pairs between left-hand sides of rules in
    * ''trs1'' and left-hand sides of rules in ''trs2''. */
  def cps(trs1: TRS, trs2: TRS): ES = {
    overlaps(trs1, trs2) map (crit_pair(_)) distinct
  }
  /** Returns a list consisting of list ''l'' with element ''r'' appended at the
    * end. 
    *
    * @tparam T the type of the list's elements */
  def end[T](l: List[T], r: T): List[T] = (r :: l.reverse).reverse
  /** Returns the list ''l'' with the ''n''-th element removed. 
    *
    * @tparam T the type of the list's elements */
  def filterNot[T](l: List[T], n: Int): List[T] = {
    val (a,b) = l.splitAt(n)
    a ::: b.tail
  }
  /** Returns a pair of two lists where the first entry is the list consisting
    * of elements from ''ls'' with indices in ''is'' and the second entry is the
    * rest of ''ls''. */
  def partition[T](is: List[Int], ls: List[T]) = {
    val (in,out) = ls.zipWithIndex.partition(x => is.contains(x._2))
    (in.map(_._1),out.map(_._1))
  }
  def combine[T](is: List[Int], xs1: List[T], ys2: List[T]) = {
    var ls = List[T]()
    var xs = xs1
    var ys = ys2
    for (i <- 0 until (xs.length+ys.length)) {
      if (is.contains(i)) {
        if (!xs.isEmpty) {
          ls =  xs.head :: ls
          xs = xs.tail
        }
      } else {
        if (!ys.isEmpty) {
          ls = ys.head :: ls
          ys = ys.tail
        }
      }
    }
    (xs ::: ys ::: ls).reverse
  }
  def longest(ls: List[Term]) = (1 /: ls.map(_.strlen))(_ max _)
}

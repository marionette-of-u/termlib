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

/** A term library.
  * 
  * This package contains a library for generating and manipulating terms,
  * various functions on terms and subpackages for parsing terms in the old
  * trs-format as well as the new xml-format, lexicographic path order, and 
  * completion.
  *
  * ==Overview==
  * [[term.package.Term]] and its subclasses [[term.package.Fun]] and
  * [[term.package.Var]] are used to 
  * represent terms. [[term.package.Pos]] implements positions in a term.
  * [[term.packge.Subst]]
  * represents substitutions on terms. */
package object term {
  import scala.collection.immutable.{TreeSet}
  import Term.{V,F}
  import util._
  import reco._
  import parser._
  import show._
  import indexing.{PString}

  case class NotMatchable(s : Term, t : Term) extends Exception
  case class InconsistentSubst(x : V, t : Term, u : Term) extends Exception {
    override def toString =
      "variable '" + x + "' cannot at the same time point to '" + t + "' and '" + u + "'"
  }
  sealed abstract class NotUnifiable extends Exception
  case class OccursCheck(x : V, t : Term) extends NotUnifiable {
    override def toString = "variable '" + x +"' occurs in term '" + t + "'"
  }
  case class SymbolClash(f : F, g : F) extends NotUnifiable {
    override def toString = "class of function symbols '" + f + "' and '" + g + "'"
  }


  /** This object contains some helping functionality and type definitions for
    * the [[term.package.Term]] class. */
  object Term {
    /** A variable is represented by a string. */
    type V = String
    /** Also a function symbol is represented by a string. */
    type F = String

    private var count = 0

    def unify(eqs : ES) : Subst = {
      def varCase(x : V, t : Term, eqs : ES, mgu : Subst) =
        if (t contains x) throw OccursCheck(x, t)
        else {
          val sub = Subst(x -> t)
          (eqs map (_(sub)), mgu(sub))
        }

      def unify_accum(eqs : ES, mgu : Subst) : Subst = eqs match {
        case Nil => mgu
        case E(s, t) :: eqs if s == t => unify_accum(eqs, mgu)
        case E(t, Var(x)) :: eqs =>
          val (eqs1, mgu1) = varCase(x, t, eqs, mgu)
          unify_accum(eqs1, mgu1)
        case E(Var(x), t) :: eqs =>
          val (eqs1, mgu1) = varCase(x, t, eqs, mgu)
          unify_accum(eqs1, mgu1)
        case E(Fun(f, ss), Fun(g, ts)) :: eqs =>
          if (f == g && ss.length == ts.length)
            unify_accum(ss.zipWith(ts)(E(_, _)) ::: eqs, mgu)
          else throw SymbolClash(f, g)
      }

      unify_accum(eqs, Subst())
    }

    def mmatch(eqs : ES) : Subst = {
      def match_accum(eqs : ES, sub : Map[V, Term]) : Subst = eqs match {
        case Nil => new Subst(sub)
        case E(t, s @ Var(x)) :: eqs => sub lift x match {
          case Some(u) =>
            if (t == u) match_accum(eqs, sub)
            else throw NotMatchable(t, s)
          case None => match_accum(eqs, sub + (x -> t))
        }
        case E(s @ Fun(f, ss), t @ Fun(g, ts)) :: eqs =>
          if (f == g && ss.length == ts.length) 
            match_accum(ss.zipWith(ts)(E(_, _)) ::: eqs, sub)
          else throw NotMatchable(s, t)
        case E(s, t) :: _ => throw NotMatchable(s, t)
      }
      match_accum(eqs, Map())
    }

    private def next(): BigInt = { count += 1; count }
  }

  import Term.{V,F}
  /** Represents a term which is built recursively from variables and function
    * symbols. 
    *
    * This class comes with two implementing case classes [[term.package.Var]]
    * and [[term.package.Fun]]. */
  sealed abstract class Term extends Ordered[Term] {
    def compare(that:Term) = size - that.size
    /** Returns ''true'' if ''this'' term is a variable and ''false'' 
      * otherwise. */
    def isVar: Boolean
    /** Returns ''[[scala.Left]](variable_name)'' if the root symbol of ''this''
      * term is a variable and ''[[scala.Right]](function_name)'' otherwise.  */
    def root: Either[V,F]
    /** Returns the list of arguments if ''this'' term is a function and 
      *[[java.lang.UnsupportedOperationException]] otherwise. */
    def args: List[Term]

    def toXML : scala.xml.Elem =
      if (isVar) <var>{root.left.get}</var>
      else <funapp>
        <name>{root.right.get}</name>
        {args.map(t => <arg>{t.toXML}</arg>)}
      </funapp>

    def addVars(xs : Set[V]) : Set[V] = this match {
      case Var(x) => xs + x
      case Fun(_, ts) => ts.foldLeft(xs)((xs, t) => t.addVars(xs))
    }

    /** Returns the set of all variables in ''this'' term. */
    def vars : Set[V] = addVars(Set())

    def addFuns(fs : Set[F]) : Set[F] = this match {
      case Var(_) => fs
      case Fun(f, ts) => ts.foldLeft(fs + f)((fs, t) => t.addFuns(fs))
    }

    /** Returns the set of all function symbols in ''this'' term. */
    def funs : Set[F] = addFuns(Set())


    def addFunAris(fs: Set[(F,Int)]) : Set[(F,Int)] = this match {
      case Var(_) => fs
      case Fun(f, ts) => 
        ts.foldLeft(fs + ((f,ts.length)))((fs, t) => t.addFunAris(fs))
    }
    def funAris : Set[(F,Int)] = addFunAris(Set())

    /** Returns the number of variables and function symbols contained in 
      * ''this'' term. */
    def size: Int = if (isVar) 1 else (1 /: args) (_ + _.size)
    /** Returns the depth of the syntax tree of ''this'' term. */
    def depth: Int =
      if (isVar || args.isEmpty) 0
      else 1 + (0 /: args) (_ max _.depth)
    /** Returns ''true'' if ''this'' term is a proper subterm of ''that'' term
      * and ''false'' otherwise. */
    def subterm(that: Term): Boolean =
      if (that.isVar) false
      else that.args.exists(subtermeq)
    /** Returns ''true'' if ''this'' term is a proper subterm of or equal to
      * ''that'' term and ''false'' otherwise. */
    def subtermeq(that: Term): Boolean = 
      this == that || this.subterm(that)

    def addSubterms(ss : Set[Term]) : Set[Term] = this match {
      case Var(x) => ss + this
      case Fun(_, ts) => ts.foldLeft(ss + this)((ss, t) => t.addSubterms(ss))
    }

    /** Returns the list of all subterms (including ''this'' term itself). */
    def subterms : Set[Term] = addSubterms(Set())

    /** Add all positions in ''this'' term, but prefixed by ''p'', to the given list
     * of positions ''ps''. Allows for an efficient implementation of ''poss''. */
    private def addPrefixedPoss(p : Pos, ps : List[Pos]) : List[Pos] = this match {
      case Var(_) => p :: ps
      // use foldRightIndex rather than foldLeftIndex to generate positions in 'natural' order
      case Fun(_, ts) => p :: ts.foldRightIndex(ps)((i, t, ps) => t.addPrefixedPoss(p ::> i+1, ps))
    }

    def addPoss(ps : List[Pos]) : List[Pos] = addPrefixedPoss(Pos(), ps)

    /** Returns the list of all positions, including the root
      * position ''epsilon'' in ''this'' term.  Note: Since,
      * by definition, every position in the result is unique,
      * we prefer 'List' over 'Set'. */
    def poss : List[Pos] = addPoss(List())

    def possStream : Stream[Pos] =
      if (isVar) Stream(Pos())
      else Pos() #:: args.toStream.zipWithIndex.flatMap {
        case (t, i) => t.possStream.map(i+1 <:: _)
      }
    /** Returns the set of all function positions in ''this'' term. */
    def possf: List[Pos] = poss.filter(!this(_).isVar)
    /** Returns the set of all variable positions in ''this'' term. */
    def possv: List[Pos] = poss.filter(this(_).isVar)
    /** Returns the subterm of ''this'' term at position ''p''. */
    def apply(p: Pos): Term = p match {
      case Pos() => this
      case i <:: q if !isVar && i <= args.length => args(i-1)(q)
      case _ => throw new NoSuchElementException("illegal position")
    }
    /** Returns ''this'' term where the subterm at position ''p'' was
      * replaced by the term ''s''. */
    def update(p: Pos, s: Term): Term = p match {
      case Pos() => s
      case i <:: q if !isVar && i <= args.length =>
        // i > 0 (due to definition of Pos)
        // together with i <= args.length (which is at least 0)
        // we know that there is at least one element in args
        // hence the following is actually complete
        (args.splitAt(i-1) : @unchecked) match {
          case (ss, t::ts) => Fun(root.right.get, ss ::: (t(q)=s) :: ts)
        }
      case _ => throw new NoSuchElementException("illegal position")
    }
    def pstring:PString = this match {
      case v @ Var(_) => List(((v,0),v))
      case f @ Fun(n,args) => ((Fun(n),args.length),f) :: args.flatMap(_.pstring)
    }
    /** Returns ''true'' if ''this'' term contains no variables and ''false''
      * otherwise. */
    def isGround = vars == Set[V]()
    /**
    * @param vcond if true enclose variables between o and c, otherwise ignore o and c
    * @param fcond if true do not use parenthesis for constants, otherwise do
    * @param o     a String to be inserted before every variable (if vcond is true)
    * @param c     a String ot be inserted after every variable (if vcond is true)
    */
    def toStringBuilder(vcond : Boolean, fcond : Boolean, o : String, c : String)
      (implicit b : ImplicitBuilder) : StringBuilder = this match {
      case Var(x) => if (vcond) b.append(o).append(x).append(c) else b.append(x)
      case Fun(f, Nil) => if (fcond) b.append(f) else b.append(f).append("()")
      case Fun(f, ts) =>
        b.append(f)
        ts.mkStringBuilder(t => b => t.toStringBuilder(vcond, fcond, o, c)(b), "(", ", ", ")")(b)
    }
    def toStringBuilder(implicit b : ImplicitBuilder) : StringBuilder =
      toStringBuilder(false, false, "", "")(b)
    /** Returns the string representation of ''this'' term. */
    override def toString = toStringBuilder.result()
    /** Returns a nicer string representation of ''this'' term where variables
      * are colored blue. Only works on Linux systems. */
    def toNiceString: String = toStringBuilder(!ms, true, Console.BLUE, Console.RESET).result()
    /** Returns a html string of ''this'' term where variables are enclosed in
      * ''<font>''-tags with blue color. */
    def toHtmlString: String = toStringBuilder(true, true, "<font color=#3d6ca8>", "</font>").result()
    /** Returns the length of the nice string version of ''this'' term 
      * (including whitespaces). */
    def strlen: Int = toStringBuilder(false, true, "", "").length()
    /** Returns ''this'' term after the substitution ''s'' was applied. */
    def apply(s: Subst): Term = this match {
      case Var(x) => s(x)
      case Fun(f,ts) => Fun(f, ts.map(_(s)))
    }
    /** Returns a unifying substitution of ''this'' and ''that'' term if they 
      * are unifiable. */
    def unify(that: Term): Subst = Term.unify(List(E(this, that)))
    /** Returns ''true'' if ''this'' and ''that'' term are unifiable and
      * ''false'' otherwise. */
    def unifiable(that: Term): Boolean = try {
      unify(that)
      true
    } catch { case _ : NotUnifiable => false }
    /** Returns a matching substitution of ''this'' and ''that'' term if they 
      * can be matched. */
    def mmatch(that : Term) : Subst = Term.mmatch(List(E(this, that)))
    /** Returns ''true'' if ''this'' term matches ''that'' term and ''false''
      * otherwise. */
    def matches(that: Term): Boolean = try {
      mmatch(that)
      true
    } catch { case _ : NotMatchable => false }
    /** Returns ''true'' if ''this'' term matches at least one of the terms in
      * ''ts''. */
    def matcheLs (ts: List[Term]): Boolean = ts.exists(this matches _)
    /** Returns ''true'' if ''that'' term mathes ''this'' term. Just the 
      * reversal of ''matches''. */
    def subsumes(that: Term): Boolean = that matches this
    def contains(x : V) : Boolean = this match {
      case Var(y) => x == y
      case Fun(_, ts) => ts exists (_ contains x)
    }
    /** Returns ''true'' if some subterm of ''this'' term subsumes ''that''
      * term. */
    def contains(that: Term): Boolean = subterms exists (_ subsumes that)
    /** Returns the term you get when applying the matching substitution from
      * ''this'' term and the left-hand side of the rule ''r'' to the right-hand
      * side of ''r''. */
    // TODO: maybe remove, only matches at root
    def contract(r: R): Term = r.rhs(this.mmatch(r.lhs))
    def contract(r: R, p:Pos):Term = this(p) = r.rhs(this(p).mmatch(r.lhs))
    def contractAtWith(s:Term,r:R):Option[(Pos,Subst)] = {
     def aux(ps:List[Pos]): Option[(Pos,Subst)] = ps match {
      case Nil => None
      case p::ps => try { 
          if (contract(r,p) == s) Some((p,(this(p).mmatch(r.lhs))))
          else aux(ps)
        } catch { case _ : NotMatchable => aux(ps) }
      } 
      aux(poss)
    }
    /** Returns the contraction of ''this'' term and some rule in the term 
      * rewrite system ''rs'' if it exists and ''this'' term otherwise. */
    def contract(rs: TRS): Term = rs match {
      case Nil => this
      case R(l,r) :: rs => if (this matches l) this contract R(l,r)
                          else this contract rs
    }
    def contract(irs: List[IR]): (Int,Term) =  irs match {
      case Nil => (-1,this)
      case (i,R(l,r)) :: irs => if (this matches l) (i,this contract R(l,r))
                                else this contract irs
    }
    /** Returns the term you get when rewriting ''this'' term one time with
      * respect to the term rewrite system ''rs'' and [[scala.None]] if no 
      * rewrite step is possible. */
    def rewriteStep(rs: TRS): Option[Term] = {
      def loop(rs: TRS, ps: List[Pos]): List[Term] = 
      ps match {
        case Nil => Nil
        case p :: ps => 
          if (this(p) matcheLs (rs map (_.lhs))) 
            (this(p) = this(p) contract rs) :: loop(rs, ps)
          else loop(rs, ps)
      }
      val results = loop(rs,poss)
      if (results.isEmpty) None else Some(results.head)
    }
    def rewriteAtWith(p:Pos,r:R):Term = (this(p) = this(p) contract r)
    def irewriteStep(irs: List[IR]): Option[(Int,Term)] = {
      def loop(irs: List[IR], ps: List[Pos]): List[(Int,Term)] = ps match {
        case Nil => Nil
        case p :: ps =>
          if (this(p) matcheLs (irs.map(_._2.lhs))) {
            val (i,t) = this(p).contract(irs)
            (i,this(p) = t) :: loop(irs,ps)
          } else loop(irs,ps)
      }
      val results = loop(irs,poss)
      if (results.isEmpty) None else Some(results.head)
    }
    def irewritableAt(irs:List[IR]):Option[Pos]={
      def aux(irs:List[IR],ps:List[Pos]):List[Pos]=ps match {
        case Nil => Nil
        case p::ps =>
          if (this(p) matcheLs (irs.map(_._2.lhs))) p::aux(irs,ps)
          else aux(irs,ps)
      }
      val results = aux(irs,poss)
      if (results.isEmpty) None else Some(results.head)
    }
    def irewritableWithSubst(ir:IR):Option[Subst]={
      def aux(ir:IR,ps:List[Pos]):List[Subst]=ps match {
        case Nil => Nil
        case p::ps =>
          if (this(p) matcheLs List(ir._2.lhs)) {
            (this(p).mmatch(ir._2.lhs))::aux(ir,ps)
          } else aux(ir,ps)
      }
      val results = aux(ir,poss)
      if (results.isEmpty) None else Some(results.head)
    }
    /** Returns the first rule from the term rewrite system ''rs'' which may be
     * used to rewrite ''this'' term and [[scala.None]] if there is no such rule
     * in ''rs''. */
    def byRule(rs: TRS): Option[R] = rs match {
      case Nil => None
      case R(l,r) :: rs => 
        if (this matches l) Some(R(l,r)) else this byRule rs
    }
    def reducibleByRule(rs: TRS): Option[R] = {
      def loop(rs: TRS, ps: List[Pos]): List[Option[R]] = 
      ps match {
        case Nil => Nil
        case p :: ps => 
          if (this(p) matcheLs (rs map (_.lhs))) 
            (this(p) byRule rs) :: loop(rs, ps)
          else loop(rs, ps)
      }
      val results = loop(rs, poss)
      if (results.isEmpty) None else results.head
    }
    /** A synonym for rewriteStep. */
    def reduce(rs: TRS): Option[Term] = rewriteStep(rs)
    def isReducible(rs: TRS): Boolean = reduce(rs) match {
      case None => false
      case _ => true
    }
    /** Returns the resulting term if ''this'' term may be rewritten with
      * respect to the term rewrite system ''rs'' and ''this'' term otherwise.
      * */
    def rewrite(rs: TRS): Term = {
      val n = rewriteStep(rs)
      if (n != None) n.get.rewrite(rs)
      else this
    }
    def rewriteToNF(itrs:ITRS):List[(Term,Int,Term)]={
      def aux(t:Term,irs:List[IR],acc:List[(Term,Int,Term)]):
      List[(Term,Int,Term)]={
        val n = t.irewriteStep(irs)
        if (n != None) aux(n.get._2,irs,(t,n.get._1,n.get._2)::acc)
        else acc.reverse
      }
      aux(this,itrs.toList,List[(Term,Int,Term)]())
    }
    /** Returns ''true'' if ''this'' term is in normal form with respect to the
      * term rewrite system ''rs'' and 'false' otherwise. */
    def isNF(rs: TRS): Boolean = {
      try { 
        rewriteStep(rs)
        false 
      } catch { case _ : NoSuchElementException => true }
    }
    /** Returns a substitution from all variables in ''this'' term to fresh
      * variables. */
    def freshVars(): Subst = {
      val vs = vars.toSeq
      if (!vs.isEmpty) {
        val ns = vs map { x => Var(x + Term.next().toString) }
        Subst(vs zip ns: _*)
      } else Subst()
    }
    /** Returns ''true'' if ''this'' term is a variant of ''that'' term and
      * ''false otherwise. */
    def variantOf(that: Term): Boolean = 
      matches(that) && mmatch(that).isRenaming
  }

  /** Represents a variable.
    * @constructor Creates a new variable.
    * @param name the name of the variable */
  case class Var(name: V) extends Term {
    /** Returns ''true''. */
    override def isVar = true
    /** Returns ''[[scala.Left]](variable_name)''. */
    override def root = Left(name)
    /** Throws a [[java.lang.UnsupportedOperationException]]. */
    override def args = 
      throw new UnsupportedOperationException("args of variable")
  }

  /** Factory for [[term.package.Fun]] instances. */
  object Fun {
    /** Creates a new function applied to some terms.
      *
      * @param name the name of the function symbol
      * @param args the terms the function is applied to */
    def apply(name: F, args: Term*): Fun = Fun(name, args.toList)
  }

  /** Represents a function.
    * @constructor Creates a new function applied to arguments.
    * @param name the name of the function symbol
    * @param args the arguments the function is applied to */
  case class Fun(name: F, args: List[Term]) extends Term {
    /** Returns ''[[scala.Right]](function_name)''. */
    override def root = Right(name)
    /** Returns ''false''. */
    override def isVar = false
  }

  /** Factory for [[term.package.Pos]] instances. */
  object Pos {
    /** Creates a position from the sequence of numbers ''args''. */
    def apply(args: Int*): Pos = new Pos(args.toList)
    /** Used in a pattern match { Pos(...) }. */
    def unapplySeq(p: Pos): Option[Seq[Int]] = Some(p.toList)
  }

  /** Factory for [[term.package.Pos]] instances. */
  object <:: {
    /** Creates a position with ''i'' prepended to ''p''. */
    def apply(i: Int, p: Pos): Pos = new Pos(i :: p.toList)
    def unapply(p: Pos): Option[(Int, Pos)] = p match {
      case Pos(i, q @ _*) => Some(i, Pos(q: _*))
      case _              => None
    }
  }

  /** Represents a position in a term.
    *
    * A position is a finite sequence of positive integers. The 
    * ''root position'' is the empty sequence. */
  class Pos(ps: List[Int]) {
    require(ps.forall(_ > 0))

    def ::>(i : Int) = new Pos(ps :+ i)

    /** Returns ''this'' position with ''i'' prepended. */
    def <::(i: Int) = term.<::(i, this)
    /** Returns ''this'' and ''that'' position appended. */
    def ++ (that: Pos) = new Pos(ps ++ that.toList) 
    /** Returns ''true'' if ''this'' position is below or equal to ''that'' 
      * position and ''false'' otherwise. */
    def <= (that: Pos) = that.toList startsWith this.ps
    /** Returns ''true'' if ''this'' position is below ''that'' position and
      * ''false'' otherwise. */
    def < (that: Pos) = this <= that && this != that
    /** Returns ''true'' if ''this'' and ''that'' position are parallel and
      * ''false'' otherwise. */
    def || (that: Pos) = !(this <= that && that <= this)
    /** Returns the number of numbers in ''this'' position. */
    def length = ps.length
    /** Returns a list containing the numbers from ''this'' position. */
    def toList = ps
    override def equals(other: Any): Boolean = other match {
      case that: Pos => (that canEqual this) && ps == that.toList
      case _ => false
    }
    def canEqual(other: Any): Boolean = other.isInstanceOf[Pos]
    override def hashCode: Int = 41 * ps.hashCode
    def toStringBuilder(implicit b : ImplicitBuilder) = toList.mkStringBuilder("Pos(", ", ", ")")(b)
    override def toString: String = toStringBuilder.result()
    def lt(that: Pos):Boolean = length < that.length
    def gte(that: Pos):Boolean = !(this lt that)
  }
  
  object Subst {
    def apply(elems : (V, Term)*) : Subst = new Subst(Map(elems : _*))
    def unapplySeq(s : Subst) : Option[Seq[(V, Term)]] = Some(s.map.toSeq)
  }

  /** Represents a substitution.
    *
    * A substitution ''sigma'' is a mapping from variables to terms such that 
    * ''x != sigma x'' for finitely many ''x'' only. 
    * 
    * @constructor Creates a new substitution from a map ''m''. */ 
  class Subst(m : Map[V, Term]) {
    // no identities allowed in substitutions, they are implicit
    private val map = m filter { case (x, t) => Var(x) != t }

    def toStringBuilder(implicit b : ImplicitBuilder) = map.mkStringBuilder("Subst(", ", ", ")")(b)
    override def toString = toStringBuilder.result()
    /** Returns the term to which the variable ''v'' is mapped in ''this''
      * substitution. */
    def apply(v: V): Term = map.getOrElse(v, Var(v))
    /** Returns the substitution which is generated by applying ''s'' to
      * ''this'' substitution. */
    def apply(s: Subst): Subst =
      Subst((map.transform((x: V, t: Term)=>t(s)) ++
        s.map.filterKeys(!map.contains(_))).toSeq: _*)
    /** Returns the set of variables which are mapped. */
    def domain: Set[V] = map.keySet
    /** Returns the set of variables introduced through the mapping. */
    def intrVars: Set[V] =
      (Set[V]() /: map.values.toList) (_ ++ _.vars)
    /** Add a new binding to a substitution. */
    def + (x : V, t : Term) : Subst = map lift x match {
      case Some(u) => if (t == u) this else throw InconsistentSubst(x, t, u)
      case None => if (Var(x) == t) this else new Subst(map + (x -> t))
    }
    def + (xt : (V, Term)) : Subst = this + (xt._1, xt._2)
    /** Returns ''this'' substitution in reversed order. */
    def rev: Subst = {
      def aux(p: (V,Term)): (V,Term) = {
        val n = p.swap
        val v = n._1 match {
          case Var(x) => x
          case _ => "x"
        }
        (v,Var(n._2))
      }
      Subst(map.toList.map(aux(_)).toSeq: _*)
    }
    /** Returns the combination of this substitution with s */
    // TODO: no two different bindings for the same variable
    def ++ (s: Subst): Subst = Subst((map ++ s.map.toList).toSeq: _*)
    /** Returns ''true'' if ''this'' substitution is just a renaming and 
      * ''false'' otherwise. */
    def isRenaming: Boolean = isVarSubst && isBijective
    private def isVarSubst: Boolean = map.toList.map(_._2).forall(_.isVar)
    private def isBijective: Boolean = length == rev.length
    // have to override, because Subst(elems: (V,Term)*) takes
    // array equals as default... (but order should not play a role here
    override def equals(other: Any): Boolean = other match {
      case that: Subst => (that canEqual this) && map == that.map
      case _ => false
    }
    /** Returns ''true'' if ''this'' substitution is a subset of ''that''
     * substitution. */
    def subsetOf(that: Subst): Boolean =
      map.forall(x => that.map.contains(x._1) && that.map(x._1) == x._2)
    def canEqual(other: Any): Boolean = other.isInstanceOf[Subst]
    override def hashCode: Int = 41 * map.hashCode
    /** Returns the number of mappings in ''this'' substitution. */
    def length: Int = map.size
    def toXML : scala.xml.Elem =
      <substitution>{map map { case (x, t) =>
        <substEntry><var>{x}</var>{t.toXML}</substEntry>
      }}</substitution>
  }
}

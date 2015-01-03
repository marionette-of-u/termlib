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

/** Provides some parsing functionality for terms.
  *
  * There are two formats for terms which can be parsed by usage of the parsers
  * in this package. A subset of the old trs format and the new xml format. */
package object parser {
  import term._
  import Term.{V,F}
  import util.{E,R,ES,TRS,vars,S}
  import reco.{IES,ITRS,IS}
  import java.io.FileReader
  import scala.util.parsing.combinator._
  import show._

  /** Represents a parser from string to an equational system. */
  trait Parser {
    /** Returns an equational system containting the equations parsed from
      * ''file''. */
    def parse(file: String): ES
  }

  /** A parser from a subset of the TPTP format to an equational proof. */
  object ParserTPTP extends RegexParsers with Parser {
    // include
    def incl(pre: String): Parser[ES] = "include"~>"("~>"'"~>path<~"'"<~")"<~"." ^^ {
      case p =>
        val q = if (pre == "") p
                else pre+java.io.File.separator+p
        parse(q)
    }
    // Name, Role, terms, Comments
    def term: Parser[Term] = varr | fun
    def varr: Parser[Term] = uid ^^ { case uid => Var(uid) }
    def fun: Parser[Term] = 
      id~opt("("~>repsep(term, ",")<~")") ^^ {
        case id~None => Fun(id,Nil)
        case id~Some(l) => Fun(id,l)
      }
    def w: Parser[Unit] = """\w*""".r ^^ { _ => () }
    def b: Parser[String] = """[A-Z]""".r
    def uid: Parser[String] = b~opt(id) ^^ { 
      case b~Some(id) => b+id 
      case b~None => b
    }
    //private def id: Parser[V] = """[a-zA-Z0-9_]\w*""".r
    //TODO: which characters should be allowed for identifiers?
    def id: Parser[String] = """[a-zA-Z0-9_:@+*.'\u00C0-\uFFE0-]\w*""".r
    def path: Parser[String] = """[a-zA-Z0-9_./\-]+""".r
    def eq: Parser[E] = term~("=" | "!=")~term ^^ { case t~_~s => E(t,s) }
    def axiom: Parser[E] = id~>"("~>id~>","~>id~>","~>"("~>eq<~")"<~")"<~"."
    def axioms: Parser[ES] = rep(axiom)
    def spec(path: String): Parser[ES] = rep(incl(path))~axioms ^^ {
      case as~a => as.flatten ++ a
    }
    //def spec: Parser[ES] = axioms ^^ { case a => a }

    /** Returns the equational system parsed from ''file'' where the last
      * equation is the conjecture to check. */
    def parse(file: String): ES = {
      val path = new java.io.File(file).getParent()
      val source = scala.io.Source.fromFile(file)
      // just throw away comments and make into String
      val input = source.getLines.filterNot(_.startsWith("%")).mkString
      source.close
      val es = parseAll(spec(path),input).getOrElse(Nil)
      es
    }
  }

  /** A parser from a subset of the old trs format to an equational system. */
  object ParserOldTRS extends RegexParsers with Parser {
    /** The list of variables used in this system. */
    var variables = List[V]()

    private def w: Parser[Unit] = """\w*""".r ^^ { _ => () }
    private def spec: Parser[(List[V],ES)] = 
      w~coms~w~vars~w~coms~w~rules~w~coms~w ^^ { case _~_~_~v~_~_~_~r~_~_~_ => (v,r) }
    private def vars: Parser[List[V]] =
      "("~"VAR"~>rep(id)<~")"
    private def coms: Parser[Unit] =
      rep("("~anylist~")") ^^ { _ => () }
    private def anylist: Parser[Unit] =
      opt(not("VAR"|"RULES")~("\""~"[^\"]*".r~"\""|id)~w~anylist |
      "("~anylist~")"~w~anylist |
      ","~w~anylist) ^^ 
      { _ => () }
    private def rules: Parser[ES] =
      "("~"RULES"~>rep(rule)<~")"
    private def inlineRules: Parser[ES] = repsep(rule, ",")
    private def rule: Parser[E] =
      opt(id~":")~term~("->" | "=" | "==" | "->=")~term ^^ 
        { case _~t~_~s => E(t,s) }
    private def term: Parser[Term] = 
      id~opt("("~>repsep(term, ",")<~")") ^^ { 
        case id~None =>
          if (variables.isEmpty || variables.contains(id)) Var(id) 
          else Fun(id,Nil)
        case id~Some(l) => Fun(id,l)
      }
    //private def id: Parser[V] = """[a-zA-Z0-9_]\w*""".r
    //TODO: which characters should be allowed for identifiers?
    private def id: Parser[V] = """[a-zA-Z0-9_:@+*.'\u00C0-\uFFE0-]\w*""".r
    /** Returns the equational system parsed from ''file''. */
    def parse(file: String): ES = {
      var reader = new FileReader(file)
      // TODO: current solution is a bit hacky and not very
      // functional! there has to be a better way!!!
      //val (v,e) = parseAll(spec, reader).getOrElse((Nil,Nil))
      //e
      variables = parse(vars, reader).getOrElse(Nil)
      reader = new FileReader(file)
      val (x,e) = parseAll(spec, reader).getOrElse((Nil,Nil))
      e
    }
    /** Returns the equational system parsed from the string ''s''. */
    def parseInline(s: String): ES = {
      parseAll(inlineRules, s).getOrElse(Nil)
    }
    def toOldStringBuilder(rs:IS,indexed:Boolean)(implicit b:ImplicitBuilder) = {
      util.vars(rs.values.toList).mkStringBuilder("(VAR ", " ", ")\n")(b)
      rs.toList.sortWith((t,s)=>t._1 < s._1).mkStringBuilder({r => b =>
        b.append("  ")
        if (indexed) {
          r._1.toStringBuilder(b)
          b.append(": ")
        }
        r._2.lhs.toStringBuilder(b)
        b.append(" -> ")
        r._2.rhs.toStringBuilder(b)
      }, "(RULES\n", "\n", "\n)")(b)
    }
    /** Returns a string representing the term rewrite system ''rs'' in the old
      * trs format. (Optionally indexed) */
    def toOldString(rs:IS,indexed:Boolean): String =
      toOldStringBuilder(rs,indexed).result()
  }

  /** A parser from the new xml format to an equational system. */
  object ParserXmlTRS extends Parser {
    /** Returns the equational system parsed from ''file''. */
    def parse(file: String): ES = {
      val node = xml.XML.loadFile(file)
      val rules = node \\ "rule"
      toEqList(rules)
    }

    private def toEqList(rules: xml.NodeSeq): ES = {
      def aux(eqs: Seq[xml.Node]): ES = eqs match {
        case Nil => Nil
        case x :: xs => toEquation(x) :: aux(xs)
      }
      aux(rules.theSeq)
    }

    private def toEquation(r: xml.Node): E =  {
      val rule = xml.Utility.trim(r)
      E(toTerm(rule \ "lhs" \ "_"), toTerm(rule \ "rhs" \ "_"))
    }

    private def toTerm(n: xml.NodeSeq): Term = n(0) match {
      case <var>{name}</var> => Var(name.toString)
      case <funapp><name>{name}</name>{args @ _*}</funapp> =>
        val ts = for (<arg>{a @ _*}</arg> <- args) yield { toTerm(a) }
        Fun(name.toString, ts.toList)
    } 

    def rulesToXML(rs : List[(Term, Term)]) : scala.xml.NodeSeq =
      <rules>{
        rs map { case (l, r) =>
          <rule><lhs>{l.toXML}</lhs><rhs>{r.toXML}</rhs></rule> }
      }</rules>

    def toXML(rs:IS):scala.xml.Elem = {
      val ss = rs.toList.sortWith((t,s)=>t._1 < s._1)
      <problem xmlns:xsi="http://www.w3.org/2001/XMLSchema-instance"
               type="termination"
               xsi:noNamespaceSchemaLocation="http://dev.aspsimon.org/xtc.xsd">
        <trs>
          <rules>{ss.map(_._2.toXML)}</rules>
          <signature>{signatureToXML(sig(ss.map(_._2)))}</signature>
        </trs>
        <strategy>FULL</strategy>
      </problem>
    }

    /*
    def eqToXML(es : ES) : scala.xml.Elem =
      <problem xmlns:xsi="http://www.w3.org/2001/XMLSchema-instance"
               type="termination"
               xsi:noNamespaceSchemaLocation="http://dev.aspsimon.org/xtc.xsd">
        <trs>
          <rules>{es.map(_.toXML)}</rules>
          <signature>{signatureToXML(eqSig(es))}</signature>
        </trs>
        <strategy>FULL</strategy>
      </problem>
      */

    private def sig(rs:S):Set[(String,Int)] = {
      def aux(t: Term): Set[(String,Int)] = t match {
        case Var(_) => Set[(String,Int)]()
        case Fun(f, args) => 
          Set[(String,Int)]((f, args.length)) ++ 
            (Set[(String,Int)]() /: args)  (_ ++ aux(_))
      }
      rs match {
        case Nil => Set[(String,Int)]()
        case e :: rs => sig(rs) ++ aux(e.lhs) ++ aux(e.rhs)
      }
    }
    /*
    private def eqSig(es: ES): Set[(String,Int)] = {
      def aux(t: Term): Set[(String,Int)] = t match {
        case Var(_) => Set[(String,Int)]()
        case Fun(f, args) => 
          Set[(String,Int)]((f, args.length)) ++ 
            (Set[(String,Int)]() /: args)  (_ ++ aux(_))
      }
      es match {
        case Nil => Set[(String,Int)]()
        case E(l,r) :: es => eqSig(es) ++ aux(l) ++ aux(r)
      }
    }
    */
    private def format(rs: Set[(String,Int)]): String = {
      def aux(rs: List[(String,Int)]): String = rs match {
        case Nil => ""
        case (f,a) :: rs => {
          "<funcsym><name>"+ f +"</name><arity>"+ a +
          "</arity></funcsym>" + aux(rs)
        }
      }
      aux(rs.toList)
    }
    private def signatureToXML(rs: Set[(String, Int)]) : scala.xml.NodeSeq =
      rs.toList.map { case (f, a) =>
        <funcsym><name>{f}</name><arity>{a}</arity></funcsym>
      }
  }
}

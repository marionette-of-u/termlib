package term

package object poly {
  import term._
  import Term.{V}
  import util._
  import scala.collection.immutable.HashMap

  sealed abstract class Coeff {
    def +(that:Coeff):Coeff = that match {
      case Zero => this
      case _ => Add(this,that)
    }
    def *(that:Coeff):Coeff = that match {
      case Zero => Zero
      case One => this
      case Add(a,b) => Add(this*a,this*b)
      case _ => Mul(this,that)
    }
    def atoms:List[Coeff] = this match {
      case Zero => Nil
      case One => Nil
      case Atom(name) => List(Atom(name))
      case Add(a,b) => a.atoms ::: b.atoms
      case Mul(a,b) => a.atoms ::: b.atoms
    }
    def toSMT:String = this match {
      case Zero => "0"
      case One => "1"
      case Atom(name) => name
      case Add(a,b) => "(+ "+a.toSMT+" "+b.toSMT+")"
      case Mul(a,b) => "(* "+a.toSMT+" "+b.toSMT+")"

    }
    def subst(hm:HashMap[String,String]):Coeff = this match {
      case Zero => Zero
      case One => One
      case Atom(name) => {
        if (hm.getOrElse(name,name) == "0") Zero
        else if (hm.getOrElse(name,name) == "1") One
        else Atom(hm.getOrElse(name,name))
      }
      case Add(a,b) => Add(a.subst(hm),b.subst(hm))
      case Mul(a,b) => Mul(a.subst(hm),b.subst(hm))
    }
  }
  case object Zero extends Coeff {
    override def +(that:Coeff):Coeff = that
    override def *(that:Coeff):Coeff = Zero
    override def toString = "0"
  }
  case object One extends Coeff {
    override def *(that:Coeff):Coeff = that
    override def toString = "1"
  }
  case class Atom(name:String) extends Coeff {
    override def toString = name
  }
  case class Add(a:Coeff,b:Coeff) extends Coeff {
    override def toString = a+" + "+b
  }
  case class Mul(a:Coeff,b:Coeff) extends Coeff {
    override def toString = a+"*"+b
  }

  object Matrix {
    def apply(dim:(Int,Int),elems:List[Coeff]) = {
      val n = dim._1*dim._2
      val l = if (elems.length <= n) elems.padTo(n,Zero) else elems.take(n)
      new Matrix(l.sliding(dim._2,dim._2).toList)
    }
    def apply(n:Int,m:Int,elems:List[Coeff]):Matrix = Matrix((n,m),elems)
    def apply(dim:Int,elems:List[Coeff]):Matrix = Matrix((dim,dim),elems)
    def apply(n:Int,m:Int,elems:Coeff*):Matrix = Matrix((n,m),elems.toList)
    def apply(dim:Int,elems:Coeff*):Matrix = Matrix(dim,elems.toList)
    def zero(dim:(Int,Int)):Matrix = Matrix(dim,Nil.padTo(dim._1*dim._2,Zero))
    def zero(n:Int,m:Int):Matrix = zero((n,m))
    def zero(dim:Int):Matrix = zero((dim,dim))
    def id(dim:Int):Matrix = {
      new Matrix(
        (for (j <- 0 until dim) yield
          (for (i <- 0 until dim) yield 
            (if (i==j) One else Zero)).toList
        ).toList
      )
    }
    def negId(dim:Int):Matrix = {
      new Matrix(
        (for (j <- 0 until dim) yield
          (for (i <- 0 until dim) yield 
            (if (i==j) Atom("-1") else Zero)).toList
        ).toList
      )
    }
  }

  class Matrix(val rows: List[List[Coeff]]) { 
    require(rows.forall(r => r.length == rows(0).length),
      "all rows has to be of same length")
    def elems = rows.flatten
    def dim = (rows.length,rows(0).length)
    def getRow(i:Int) = rows(i)
    def getColumn(j:Int) = (for (r <- rows) yield r(j)).toList
    def get(i:Int,j:Int) = rows(i)(j)
    def +(that:Matrix):Matrix = {
      require(dim == that.dim,"dimensions have to be aqual")
      new Matrix((for (i <- 0 until dim._1) yield
        (for ((a,b) <- rows(i) zip that.rows(i)) yield 
          a + b
        ).toList
      ).toList)
    }
    def *(that:Matrix):Matrix = {
      require(dim._2 == that.dim._1,
        "dimensions have to fit: n x m * m x k = n x k")
      new Matrix((for (i <- 0 until dim._1) yield
        (
          (for (j <- 0 until that.dim._2) yield {
            (getRow(i) zip that.getColumn(j)).map(t => t._1 * t._2).reduce(_ + _)
          }).toList
        )
      ).toList)
    }
    override def equals(other: Any): Boolean = other match {
      case that: Matrix => (that canEqual this) && elems == that.elems
      case _ => false
    }
    def canEqual(other: Any): Boolean = other.isInstanceOf[Matrix]
    override def hashCode: Int = 73 * elems.hashCode
    def isZero:Boolean = this == Matrix.zero(dim)
    def isId:Boolean = this == Matrix.id(dim._1)
    def isNegId:Boolean = this == Matrix.negId(dim._1)
    override def toString = 
      if (dim == (1,1))
        (for (r <- rows) yield r.mkString(" ")).mkString("","; ","")
      else
        (for (r <- rows) yield r.mkString(" ")).mkString("[","; ","]")
    def toHtmlString =
      if (dim == (1,1))
        "<table cellspacing='0' cellpadding='0'><tr><td>"+
        (for (r <- rows) yield r.mkString(" ")).mkString("",";","")+
        "</td></tr></table>"
      else {
        val b = "<td style='width:1px;background:black'>&nbsp</tb>"
        (for (r <- rows) yield r.map(t => "<td align='center'"+
        " style='padding-left:3px;padding-right:3px'>"+t+"</td>").
          mkString("<tr>"+b,"",b+"</tr>")).
            mkString("<table cellpadding='0' cellspacing='0'"+
            " style='padding-left:5px;padding-right:5px'>","","</table>")
      }
    def subst(hm:HashMap[String,String]) = Matrix(dim,elems.map(_.subst(hm)))
  }
  abstract sealed trait Poly {
    def +(that:Poly):Poly
    override def toString = this match {
      case Const(c) => c.toString
      case Monom(c,v) => {
        val va = (if (!ms) Console.BLUE+v+Console.RESET else v)
        if (c.isId) va
        else if (c.isNegId) "-"+va
        else c+""+va
      }
      case Polynom(ms,c) => {
        val ns = ms.filter(m => !m.c.isZero)
        ns.mkString(""," + ","") + 
        (if (ns.isEmpty) c.toString
         else if (c.c.isZero) ""
         else " + "+c)
      }
    }
    def toHtmlString:String = this match {
      case Const(c) => c.toHtmlString
      case Monom(c,v) =>
        if (c.isId) "<td><font color=#3d6ca8>"+v+"</font></td>"
        else if (c.isNegId) "<td>-<font color=#3d6ca8>"+v+"</font></td>"
        else
          "<td>"+c.toHtmlString + "</td><td><font color=#3d6ca8>"+v+
          "</font></td>"
      case Polynom(ms,c) => {
        val ns = ms.filter(m => !m.c.isZero).map(_.toHtmlString)
        "<table cellpadding='0' cellspacing='0'><tr>"+
        ns.mkString("","<td>&nbsp;+&nbsp;</td>","") + 
        (if (ns.isEmpty) "<td>"+c.toHtmlString+"</td>"
         else if (c.c.isZero) ""
         else "<td>&nbsp;+&nbsp;</td><td>"+c.toHtmlString+"</td>")+
        "</tr></table>"
      }
    }
    def subst(hm:HashMap[String,String]):Poly = this match {
      case Const(c) => Const(c.subst(hm))
      case Monom(c,v) => Monom(c.subst(hm),v)
      case Polynom(ms,c) => Polynom(ms.map(_.subst(hm)),c.subst(hm))
    }
    def normalize:Polynom = this match {
      case Const(c) => Polynom(Nil,Const(c))
      case Monom(c,v) => Polynom(List(Monom(c,v)),Const(Matrix.zero(c.dim._1,1)))
      case Polynom(ms,c) => Polynom(ms,c)
    }
  }
  case class Const(c:Matrix) extends Poly {
    def +(that:Poly):Poly = that match {
      case Const(c2) => Const(c+c2)
      case Monom(c,v) => Polynom(List(Monom(c,v)),this)
      case Polynom(ms,c2) => Polynom(ms,Const(c2.c+c))
    }
    override def subst(hm:HashMap[String,String]):Const = Const(c.subst(hm))
  }
  case class Monom(c:Matrix,v:V) extends Poly {
    def +(that:Poly):Poly = that match {
      case Const(c2) => Polynom(List(this),Const(c2))
      case Monom(c2,v2) => 
        if (v == v2) Monom(c+c2,v)
        else Polynom(List(this,Monom(c2,v2)),Const(Matrix.zero((this.c.dim._1,1))))
      case Polynom(ms,c2) => Polynom(ms,c2)+this
    }
    override def subst(hm:HashMap[String,String]):Monom = Monom(c.subst(hm),v)
  }
  case class Polynom(ms:List[Monom],c:Const) extends Poly {
    def +(that:Poly):Poly = that match {
      case Const(c2) => Polynom(ms,Const(c.c+c2))
      case Monom(c2,v2) => {
        Polynom(insert(ms,Monom(c2,v2)),c)
      }
      case Polynom(ms2,c2) => {
        Polynom(insert(ms,ms2),Const(c.c+c2.c))
      }
    }
    private def insert(ls:List[Monom],m:Monom):List[Monom] = ls match {
      case Nil => List(m)
      case x::xs => if (x.v == m.v) Monom(x.c+m.c,x.v) :: xs else x::insert(xs,m)
    }
    private def insert(ls:List[Monom],ns:List[Monom]):List[Monom] = ns match {
      case Nil => ls
      case x::xs => insert(insert(ls,x),xs)
    }
  }
  class Interpretation(val dim:Int) {
    val secMap:HashMap[String,String] = HashMap(
      "0" -> "secMapZero",
      "1" -> "secMapOne",
      "+" -> "secMapPlus",
      "-" -> "secMapMinus",
      "*" -> "secMapTimes",
      "!" -> "secMapExMark",
      "=" -> "secMapEquals"
    )
    def interpret(t:Term):Poly = t match {
      case Var(x) => Monom(Matrix.id(dim),x)
      case Fun(f,fs) => {
        val name = secMap.getOrElse(f,f)
        val arity = fs.length
        val matrices: List[Matrix] =
          (for (m <- 0 until arity) yield
            new Matrix(
              (for (i <- 0 until dim) yield 
                (for (j <- 0 until dim) yield 
                  Atom(name+""+m+""+i+""+j)).toList 
              ).toList
            )
          ).toList
        val vector:Matrix = 
          Matrix((dim,1),(for (i <- 0 until dim) yield Atom(name+""+i)).toList)
        (for (i <- 0 until matrices.length) yield {
          mul(matrices(i),interpret(fs(i)))
        }).toList.reverse.foldRight(Const(vector):Poly)(_ + _)
      }
    }
    override def toString = "Interpretation("+dim+")"
    def interpret(e:E):(Poly,Poly) = (interpret(e.lhs),interpret(e.rhs))
    private def mul(m:Matrix,p:Poly):Poly = p match {
      case Const(c) => Const(m*c)
      case Monom(c,v) => Monom(m*c,v)
      case Polynom(ms,c) =>
        Polynom(ms.map(n => Monom(m * n.c,n.v)),Const(m * c.c))
    }
    def interpret(es:ES):List[(Poly,Poly)] = es match {
      case Nil => Nil
      case e :: es => interpret(e) :: interpret(es)
    }
    private def getAtoms(p:Poly):List[Coeff] = p match {
      case Const(c) => c.elems.map(_.atoms).flatten
      case Monom(c,v) => c.elems.map(_.atoms).flatten
      case Polynom(ms,c) => 
        (ms.map(m => getAtoms(m)).flatten ::: c.c.elems.map(_.atoms).flatten).distinct
    }
    private def generateVars(ps:List[(Poly,Poly)]):String = {
      def aux (ps:List[(Poly,Poly)]):List[Coeff] = ps match {
        case Nil => Nil
        case p :: ps => (getAtoms(p._1) ::: getAtoms(p._2)) ::: aux(ps)
      }
      val l = aux(ps).distinct.sortWith((t,s) => t.toString() < s.toString())
        l.map(e => " :extrafuns (("+e+" Int))").mkString("\n")
    }
    private def generateEqs(b:Boolean,es:ES):String={
      val ps = interpret(es)
      val eqs = ps.map(generateEq(b,_)).flatten
      if (b) eqs.mkString("\n")
      else " :assumption (or "+eqs.mkString(" ")+")"
    }
    private def generateEq(b:Boolean,p:(Poly,Poly)):List[String] = {
      val p1 = p._1.normalize
      val p2 = p._2.normalize
      import scala.collection.mutable.HashMap
      val hm = new HashMap[V,Unit]
      val t1:List[String] =
        (for (m <- p1.ms) yield {
          val opt = p2.ms.find(n => n.v == m.v)
          if (opt.isEmpty) {
            // equal to zero
            generateEq(b,m.c,Matrix.zero(m.c.dim))
          } else {
            hm += ((m.v,()))
            generateEq(b,m.c,opt.get.c)
          }
        }).toList.flatten
      val t2:List[String] =
        (for (m <- p2.ms) yield {
          if (!hm.contains(m.v)) {
            generateEq(b,Matrix.zero(m.c.dim),m.c)
          } else Nil
        }).toList.flatten
      val t3:List[String] = generateEq(b,p1.c.c,p2.c.c)
      (t1 ::: t2 ::: t3)
    }
    private def generateEq(b:Boolean,m1:Matrix,m2:Matrix):List[String] =
      (for ((e1,e2) <- m1.elems zip m2.elems) yield
        (if (b) " :assumption (= " else "(not (= ")+
        e1.toSMT+" "+e2.toSMT+
        (if (b) ")" else "))"))
    def generateSMTString(es:ES,e:E):String = {
      val ps = interpret(es)
      val ps2 = interpret(List(e))
      "(benchmark none\n :logic QF_NIA\n"+
      generateVars(ps:::ps2)+"\n"+
      generateEqs(true,es)+"\n"+
      generateEqs(false,List(e))+"\n"+
      " :formula true\n)\n"
    }
  }
  
  val a:Coeff = Atom("a")
  val b:Coeff = Atom("b")
  val c:Coeff = Atom("c")
  val d:Coeff = Atom("d")
  val e:Coeff = Atom("e")

  val x = Var("x")
  val y = Var("y")
  val f = Fun("f",x)
  val ff = Fun("f",f)
  val g = Fun("g",x)
  val gg = Fun("g",g)
  val ggf = Fun("f",gg)
  val gf = Fun("g",f)
  val fgf = Fun("f",gf)
  val fgg = Fun("f",gg)
  val h = Fun("h",x,y)
  val mx = Matrix((2,1),List(Atom("x1"),Atom("x2")))
  val m = Matrix(2,a,b,c,d)
  val i = new Interpretation(2)
  val e1:E = E(ff,f)
  val e2:E = E(ggf,g)
  val e3:E = E(fgf,fgg)
  val e4:E = E(f,g)
  val es = List(e1,e2)
}

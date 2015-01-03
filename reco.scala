package term

package object reco {
  import term._
  import term.Term.{V}
  import util._
  import lpo._
  import parser._
  import indexing.{TermIndex,DT}
  import scala.collection.immutable.TreeMap
  import scala.collection.immutable.HashMap
  import scala.collection.immutable.HashSet
  import scala.collection.immutable.Set
  import scala.collection.immutable.SortedMap
  import scala.concurrent._
  import scala.concurrent.duration.Duration
  import scala.concurrent.Await._
  import scala.concurrent.ExecutionContext.Implicits.global
  import scala.util.control.Breaks._

  private var threads = 0
  private lazy val execSingle = ExecutionContext.fromExecutor(java.util.concurrent.Executors.newSingleThreadExecutor())

  def setSingle = threads = 1
  private def getEC = if (threads == 1) execSingle else global

  object Rel extends Enumeration {
    type Rel = Value
    val LR, RL, EQ = Value
  }
  import Rel._

  private object Simp extends Enumeration {
    type Simp = Value
    val EqL, EqR, RuL, RuR = Value
  }
  import Simp._

  /** A termination method (TM) is a function which yields ''true'' if a given
    * term rewrite system terminates and ''false'' otherwise. Optionally it also
    * returns the found [[term.lpo.Precedence]]. */
  type TM = ITRS => (Boolean,OP)
  type OP = Option[Precedence]
  type IES = TreeMap[Int,E]
  type ITRS = TreeMap[Int,R]
  type IS = TreeMap[Int,TermPair]
  type IR = (Int,R)
  type IE = (Int,E)
  type IT = (Int,TermPair)
  type OL = (IR,Pos,IR)
  type O = (Int,Rel)
  type HE = (Term,O,Term,O,Term)
  type IH = (Int,HE)
  type H = TreeMap[Int,HE]
  type ERCH = (IES,ITRS,ITRS,H)
  type J = (Term,O,Term)
  type JS = List[J]
  type Row = (J,String,JS)
  type I = Set[Int]
  type OLS = HashSet[(Int,Int)]
  type S = Map[Int,I]
  type TI = TermIndex

  /** Returns ''true'' if ''rs'' is complete and has the same conversion as
    * ''es'' and ''false otherwise.  */
  def isComplete(ols:OLS,ti:TI)(erch:ERCH):Boolean =
    erch._1.isEmpty && !erch._2.isEmpty && allCPsAreJoinable(ols,ti)(erch) 
  private def allCPsAreJoinable(ols:OLS,ti:TI)(erch:ERCH):Boolean = {
    val (_,rs,_,_) = erch
    val trs = rs.values.toList
    val (cps,_,_,_) = deduce(ols,ti)(rs.keySet,erch)
    (for ((_,e) <- cps) yield {future {e.isJoinable(trs)}(getEC)}).
      toList.map(result(_,Duration.Inf)).forall(t => t)
  }
  private def deduce(ols:OLS,ti:TI,is:I,erch:ERCH,gen:Boolean,eff:Boolean):ERCH = {
    val (es,rs,cs,hs) = erch
    val (in,out) = partition(is,rs)
    val rs1 = in.toList
    val rs2 = if (gen) Nil else if (eff) rs.toList else out.toList
    def o(ols:OLS,r:List[IR],s:List[IR]) = overlaps(ols,ti,r,s,oToHe _)
    val os = (o(ols,rs1,rs2):::o(ols,rs2,rs1):::o(ols,rs1,rs1))
    val cos = os.flatMap(f => result(f,Duration.Inf))
    val cps = cos.distinct
    val em = m(hs)
    val nis = (em until em+cps.length).toList
    val hs1 = new H ++ (nis zip cps)
    val nes = hs1.mapValues(v => E(v._1,v._5))
    (es ++ nes,rs,cs,hs ++ hs1)
  }
  def deduce(ols:OLS,ti:TI)(is:I,erch:ERCH):ERCH = deduce(ols,ti,is,erch,true,false)
  def deduceE(ols:OLS,ti:TI)(is:I,erch:ERCH):ERCH = deduce(ols,ti,is,erch,false,true)
  def deduceS(ols:OLS,ti:TI)(is:I,erch:ERCH):ERCH = deduce(ols,ti,is,erch,false,false)

  private def orient(is:I,erch:ERCH,tm:TM,lhs:Boolean):(ERCH,OP) = {
    val (es,rs,cs,hs) = erch
    val (in,out) = partition(is,es)
    def toRule(e:IE) = if (lhs) (e._1,e._2.toRule) else (e._1,e._2.swap.toRule)
    def f(r:IR) = rs.toSet.contains(r._2)
    val ts = in.map(toRule(_)).filterNot(f(_))
    val cs1 = cs ++ ts
    val (t,p) = tm(cs1)
    val hs1 = if (lhs) hs else hs ++ partition(is,hs)._1.map(t=>(t._1,swap(t._2)))
    if (t) ((out,rs ++ ts,cs1,hs1),p) else (erch,p)
  }
  def orientL(is:I,erch:ERCH,tm:TM):(ERCH,OP) = orient(is,erch,tm,true)
  def orientR(is:I,erch:ERCH,tm:TM):(ERCH,OP) = orient(is,erch,tm,false)
  def orient(is:I,erch:ERCH,tm:TM):(ERCH,OP) = {
    val (next,p) = orientL(is,erch,tm)
    if (next != erch) (next,p) else orientR(is,erch,tm)
  }

  private def concurrentSimpToNF(count:Int,depth:Int,cache:S,ti:TI,is:I,erch:ERCH,s:Simp):ERCH =
  if (is.isEmpty || count >= depth) erch else {
    val (es,rs,cs,hs) = erch
    val es1 = s match { case EqL | EqR => partition(is,es)._1 case _ => es }
    val rs1 = s match { case RuL | RuR => partition(is,rs)._1 case _ => rs }
    val xs = s match { case EqL | EqR => es1 case _ => rs1 }
    val fhs = history(cache,ti,xs.toList,rs.toList,s)
    val chs = fhs.map(f => result(f,Duration.Inf))
    val phs = chs.filter(_.isDefined).map(_.get)
    val sis = phs.map(s match { case EqL | RuL => _._4._1 case _ => _._2._1}).toSet
    def c(i:Int) = sis.contains(i)
    val em = m(hs)
    val nis = (em until em+phs.size).toSet
    val nhs = new H ++ (nis zip phs)
    val nes = s match { case RuR => new IES case _ => nhs.mapValues(v => E(v._1,v._5)) }
    val nrs = s match { case RuR => nhs.mapValues(v => R(v._1,v._5)) case _ => new ITRS }
    val es2 = s match { case EqL | EqR => es.filterNot(e => c(e._1)) case _ => es }
    val rs2 = s match { case RuL | RuR => rs.filterNot(r => c(r._1)) case _ => rs }
    val nerch = (es2 ++ nes,rs2 ++ nrs,rs2 ++ nrs,hs ++ nhs)
    concurrentSimpToNF(count+1,depth,cache,ti,nis,nerch,s)
  }
  def simplifyToNF(simps:S,ti:TI,depth:Int)(is:I,erch:ERCH):ERCH = {
    val (es,rs,cs,_) = erch
    val (es1,_,_,hs1) = concurrentSimpToNF(0,depth,simps,ti,is,erch,EqL)
    val newis = (es1.keySet &~ es.keySet)
    val uncis = is & es1.keySet
    val nis:I = uncis ++ newis
    concurrentSimpToNF(0,depth,simps,ti,nis,(es1,rs,cs,hs1),EqR)
  }

  def delete(is:I,erch:ERCH):ERCH = {
    val (es,rs,cs,hs) = erch
    val (out,in) = es.partition {case (k,v) => is.contains(k) && v.lhs == v.rhs}
    (in,rs,cs,hs.filterNot { case (k,v) => out.keySet.contains(k) })
  }

  def composeToNF(comps:S,ti:TI,depth:Int)(is:I,erch:ERCH):ERCH =
    concurrentSimpToNF(0,depth,comps,ti,is,erch,RuR)

  def collapse(colls:S,ti:TI)(is:I,erch:ERCH):ERCH =
    concurrentSimpToNF(0,1,colls,ti,is,erch,RuL)

  def he(ie:(Int,TermPair),ir:IR,u:Term,c:Simp):HE = {
    val (i,e) = ie
    val (t,s) = (e.lhs,e.rhs)
    val j = ir._1
    c match {
      case EqL | RuL => (u,(j,RL),t,(i,LR),s)
      case _ => (t,(i,LR),s,(j,LR),u)
    }
  }

  private def init(ol:OL) = {
    val (e1,p,e2) = ol
    val (l1n,r1n) = (e1._2.lhs, e1._2.rhs)
    val rn2 = e2._2.lhs.freshVars
    val (l2n,r2n) = (e2._2.lhs(rn2), e2._2.rhs(rn2))
    val sub = l1n(p) unify l2n
    // vars which are already there
    val vars1 = l1n.vars -- l1n(p).vars
    // vars which are to be renamed in a sane way
    val vars2 = l1n(sub)(p).vars ++ r2n(sub).vars
    // sane renaming
    val ren = saneVars(vars1, vars2)
    (e1,p,e2,l1n,r1n,l2n,r2n,sub,ren)
  }

  private def oToHe(ol:OL):HE = {
    val (e1,p,e2,l1n,r1n,l2n,r2n,sub,ren) = init(ol)
    (
      (l1n(sub)(p) = r2n(sub))(ren), 
      (e2._1,RL),
      (l1n(sub)(p) = l2n(sub))(ren),
      (e1._1,LR),
      r1n(sub)(ren)
    ) 
  }

  private def crit_pair(ol:OL):(Term,Int,Pos,Int,Term)={
    val (e1,p,e2,l1n,r1n,l2n,r2n,sub,ren) = init(ol)
    (
      (l1n(sub)(p) = r2n(sub))(ren), 
      e2._1,
      p,
      e1._1,
      r1n(sub)(ren)
    ) 
  }
  private def pcpnb(itrs:ITRS)(ol:OL):(Term,Int,Pos,Int,Term,Boolean,Boolean)={
    val (e1,p,e2,l1n,r1n,l2n,r2n,sub,ren) = init(ol)
    val rs = itrs.values.toList
    val s = l2n(sub)(ren)
    val ss = (s.subterms - s)
    val vars = (l1n.vars ++ l2n.vars).map(Var(_)(sub))
    (
      (l1n(sub)(p) = r2n(sub))(ren), 
      e2._1,
      p,
      e1._1,
      r1n(sub)(ren),
      !ss.exists(_.isReducible(rs)),
      !vars.exists(_.isReducible(rs))
    ) 
  }
  def critical_pairs(itrs:ITRS):List[(Term,Int,Pos,Int,Term,Boolean,Boolean)]={
    val rs = itrs.toList
    //val os = overlaps(new OLS,DT.empty,rs,rs,crit_pair _).distinct
    val os = overlaps(new OLS,DT.empty,rs,rs,pcpnb(itrs) _).distinct
    os.flatMap(f => result(f,Duration.Inf))
  }

  def m(h:H) = (try { h.keys.max } catch { case _ => -1})+1

  def partition[K,V](is:Set[K],hm:TreeMap[K,V]) = hm.partition(t => is.contains(t._1))

  private def swap(he:HE):HE = (he._5,swap(he._4),he._3,swap(he._2),he._1)
  
  private def swap(o:O):O = o match {
    case (x,LR) => (x,RL)
    case (x,RL) => (x,LR)
    case _ => o
  }
 
  def overlaps[F](ols:OLS,ti:TI,ss:List[IR],rs:List[IR],t:(OL => F)=((x:OL) => x)):List[Future[List[F]]]=
    ss.flatMap(r => {
      val rs2 = rs.filterNot(x => ols.contains((x._1,r._1)))
      r._2.lhs.possf.map(p => future {
        val is = ti.units(r._2.lhs(p))
        val rs3 = if (ti == DT.empty) rs2 else rs2.filter(x => is.contains(x._1))
        rs3.map(s => {
          val rn1 = r._2.lhs.freshVars
          val r1 = r._2(rn1)
          val rn2 = s._2.lhs.freshVars
          val r2 = s._2(rn2)
          if (r1.lhs(p).unifiable(r2.lhs) && r1.check(p,r2))
            List(t((r,p,s)))
          else Nil
        }).flatten
      }(getEC))
  })

  def history(simps:S,ti:TI,ts:List[IT],rs:List[IR],c:Simp):List[Future[Option[HE]]] = ts.map(t => future {
    val rs1 =
      if (simps.isDefinedAt(t._1)) rs.filterNot { case (i,r) => simps(t._1).contains(i) }
      else rs
    def f(t:IT) = c match {
      case EqL | RuL => t._2.lhs
      case _ => t._2.rhs
    }
    var res:Option[HE] = None
    breakable {
      val s = f(t)
      for (p <- s.poss) {
        val u = s(p)
        val is = ti.gents(u)
        val rs2 = if (ti == DT.empty) rs1 else rs1.filter(x => is.contains(x._1))
        for (r <- rs2) {
          if (c != RuL || !r._2.lhs.isReducible(List(R(t._2.lhs,t._2.rhs))))
            res = if (u.matches(r._2.lhs)) Some(s(p) = u.contract(r._2)).map(x => he(t,r,x,c))
                  else None
          if (res.isDefined) break
        }
      }
    }
    res
  }(getEC))
    
  def initHistory(ies:IES):H =
    new H ++ ies.toList.map(e => (e._1,(e._2.lhs,(e._1,LR),e._2.rhs,(e._1,EQ),e._2.rhs)))

  def joiningSequence(s:Term,t:Term,itrs:ITRS,e0:IES,h:H):Option[JS] = {
    //println("s: "+s)
    //println("t: "+t)
    val sjs = s.rewriteToNF(itrs)
    val tjs = t.rewriteToNF(itrs)
    //println("sjs: "+sjs)
    //println("tjs: "+tjs)
    val snf = if (!sjs.isEmpty) sjs.reverse.head._3 else s
    val tnf = if (!tjs.isEmpty) tjs.reverse.head._3 else t
    //println("snf: "+snf)
    //println("tnf: "+tnf)
    if (snf==tnf) {
      val ss = sjs.map(t=>(t._1,(t._2,LR),t._3))
      val ts = tjs.reverse.map(t=>(t._3,(t._2,RL),t._1))
      //println("ss: "+ss)
      //println("ts: "+ts)
      Some(shorten(ss:::ts))
    } else None
  }
  /** If ''t'' is matchable at some position with ''s'' and ''u'' is also
    * matchable at the same position with ''v'' this function returns this 
    * position together with the matching substitution. 
    * Otherwise it returns [[scala.None]]. */
  def getPosAndSubst(t:Term,s:Term,u:Term,v:Term):Option[(Pos,Subst)] =
    rewriteStep(s, v, t, u)
  /** Check whether there is a root rewrite step from 's' to 't' using
    * the rule (l, r). */
  def rootStep(l : Term, r : Term, s : Term, t : Term) : Option[Subst] = {
    import scala.collection.immutable.TreeMap
    try {
      val list = List(E(s, l), E(t, r))
      val subst = Term.mmatch(list)
      Some(subst)
    } catch { case _ : NotMatchable => None }
  }
  /** Check whether there is a rewrite step from 's' to 't' using
    * the rule '(l, r)'. */
  def rewriteStep(l : Term, r : Term, s : Term, t : Term) : Option[(Pos, Subst)] = {
    case object ContextsDoNotMatch extends Exception
    // a rewrite step takes place either at the root
    // or at some argument
    def aux(s : Term, t : Term) : Option[(Pos, Subst)] = {
      rootStep(l, r, s, t) match {
        case Some(subst) => Some((Pos(), subst))
        case None =>
          (s, t) match {
            // make sure that the contexts coincide
            case (Fun(g, ss), Fun(f, ts)) =>
              if (g != f) throw ContextsDoNotMatch
              // the arguments upto position i are implicitly checked
              // since aux is applied from left to right
              else {
                (ss zip ts) indexOption { case (s, t) => aux(s, t) } map {
                  case (i, (p, subst)) => 
                    val j = i + 1
                    if (ss.drop(j) != ts.drop(j)) throw ContextsDoNotMatch
                    else (i+1 <:: p, subst)
                }
              }
            case _ =>
              if (s != t) throw ContextsDoNotMatch
              else None
          }
      }
    }
    try { aux(s, t) } catch { case ContextsDoNotMatch => None }
  }
  def recall(js:JS,e0:IES,h:H):JS = js match {
    case Nil => Nil
    case (s1,(i,o),s2)::ss => {
      if (e0.contains(i)) { // index is in e0
        // check if the equation was oriented RL and mirror accordingly
        val on = if (h(i)._2._2 == LR) (i,o) else swap((i,o))
        (s1,on,s2)::recall(ss,e0,h)
      } else { // index is not in e0
        val (t1,o1,t2,o2,t3) = h(i)
        if (o == LR) {
          val (p,subst) = getPosAndSubst(s1,t1,s2,t3).get
          val t4 = (s1(p) = (t2(subst)))
          recall((s1,o1,t4)::(t4,o2,s2)::ss,e0,h)
        } else {
          val (p,subst) = getPosAndSubst(s2,t1,s1,t3).get
          val t4 = (s2(p) = (t2(subst)))
          recall((s1,swap(o2),t4)::(t4,swap(o1),s2)::ss,e0,h)
        }
      }
    }
  }
  def recall(u1:Term,u2:Term,e0:IES,r:ITRS,h:H):JS={
    val js = joiningSequence(u1,u2,r,e0,h)
    val res = recall(js.get,e0,h)
    shorten(res)
  }
  def recall(i:Int,e0:IES,h:H):JS={
    val he = h(i)
    val js = List((he._1,he._2,he._3),(he._3,he._4,he._5))
    recall(js,e0,h)
  }
  def orig(i:Int,e0:IES,e:IES,r:ITRS,h:H):Int={
    val he = h(i)
    val j = he._2._1;
    val k = he._4._1;
    if (!e0.contains(i) && !r.contains(j) && !e.contains(j)) orig(j,e0,e,r,h)
    else if (!e0.contains(i) && !r.contains(k) && !e.contains(k)) orig(k,e0,e,r,h)
    else i;
  }
  def shorten(js:JS):JS={
    def aux(ss:JS,acc:JS):JS=ss match {
      case Nil => acc.reverse
      case s::ss => {
        val nr = aux2(s._3,ss.reverse,Nil)
        if ((acc++(s::nr)).length == js.length) aux(ss,s::acc)
        else (s::acc).reverse++nr
      }
    }
    def aux2(t:Term,js:JS,acc:JS):JS=js match {
      case Nil => acc
      case j::js => if (j._1 == t) j::acc else aux2(t,js,j::acc)
    }
    aux(js,Nil)
  }
  def plant2(s:Term,t:Term,js:JS):ProofTree={
    def aux(js:JS,pt:ProofTree):ProofTree= js match {
      case Nil => pt
      case j::js => {
        val pt1 = APP(j)
        aux(js,TRA((pt.eq._1,(0,EQ),j._3),pt,pt1))
      }
    }
    if (js.isEmpty) REF((s,(0,EQ),t))
    else if (js.length == 1) APP(js.head)
    else {
      val j1 = js.head
      val j2 = js.tail.head
      val rest = js.tail.tail
      val pt1 = APP(j1) 
      val pt2 = APP(j2)
      aux(rest,TRA((j1._1,(0,EQ),j2._3),pt1,pt2))
    }
  }
  private def app(e:E,eq:E):Boolean={
    try {
      Term.mmatch(List(E(e.lhs, eq.lhs), E(e.rhs, eq.rhs)))
      true
    } catch { case _ : NotMatchable => false }
  }
  // returns true if e is equal to some e1 from es together with some sigma
  def application(e:E,es:IES):Boolean=es.exists(t=>app(e,t._2))
  def application2(e:E,es:IES):Int=es.filter(t=>app(e,t._2)).head._1

  sealed abstract class ProofTree {
    def eq:J
    def subTrees:List[ProofTree] = this match {
      case CON(_,pts) => pts
      case TRA(_,pt1,pt2) => List(pt1,pt2)
      case SYM(_,pt) => List(pt)
      case _ => Nil
    }
    def rule:String = this match {
      //case EQU(_) => "Equ"
      case REF(_) => "Ref"
      case APP(_) => "App"
      case SYM(_,_) => "Sym"
      case TRA(_,_,_) => "Tra"
      case CON(_,_) => "Con"
    }
    def grow(e0:IES):ProofTree= /*this match*/ {
      val pts = this.subTrees
      val eq = this.eq
      if (pts.isEmpty) {
        val (lhs,(i,rel),rhs) = eq
        // 1. reflexivity
        if (lhs == rhs) {
          REF(eq)
        // 2. symmetry NEEDS TO BE BEFORE application
        } else if (rel == RL) {
          val pt1 = APP((rhs,(i,LR),lhs))
          SYM(eq,pt1.grow(e0))
        // 3. application
        } else if (application(E(lhs,rhs),e0)) {
          APP((lhs,(application2(E(lhs,rhs),e0),rel),rhs))
        // 4. congruence
        } else if (lhs.root == rhs.root) {
          val nargs = (lhs.args zip rhs.args).map(p=>(
            APP((p._1,(0,EQ),p._2))
          ))
          CON(eq,nargs.map(_.grow(e0)))
        // ??? error ???
        } else this
      } else {
        this match {
          case SYM(eq,pt) => SYM(eq,pt.grow(e0))
          case CON(eq,pts) => CON(eq,pts.map(_.grow(e0)))
          case TRA(eq,pt1,pt2) => TRA(eq,pt1.grow(e0),pt2.grow(e0))
          case pt => pt
        }
      }
      /*
      case EQU(eq) => {
        val (lhs,(i,rel),rhs) = eq
        // 1. reflexivity
        if (lhs == rhs) {
          REF(eq)
        // 2. symmetry NEEDS TO BE BEFORE application
        } else if (rel == RL) {
          val pt1 = APP((rhs,(i,LR),lhs))
          SYM(eq,pt1.grow(e0))
        // 3. application
        } else if (application(E(lhs,rhs),e0)) {
          APP((lhs,(application2(E(lhs,rhs),e0),rel),rhs))
        // 4. congruence
        } else if (lhs.root == rhs.root) {
          val nargs = (lhs.args zip rhs.args).map(p=>(
            EQU((p._1,(0,EQ),p._2))
          ))
          CON(eq,nargs.map(_.grow(e0)))
        // ??? error ???
        } else this
      }
      case TRA(eq,pt1,pt2) => TRA(eq,pt1.grow(e0),pt2.grow(e0))
      case pt => pt
      */
    }
    def fold[T](f:(ProofTree,T)=>T,z:T):T={
      def aux(t:ProofTree,z:T):T = f(t,t.subTrees.reverse.foldRight(z)(aux))
      aux(this,z)
    }
    def linesAndHash(e0:IES):(List[Row],HashMap[J,Int])={
      val s = e0.size
      def aux(t:ProofTree,xs:(List[Row],HashMap[J,Int])):
        (List[Row],HashMap[J,Int])={
        val line = (t.eq,t.rule,t.subTrees.map(_.eq))
        if (xs._2 contains t.eq) xs
        else (line::xs._1,xs._2 + ((t.eq,
          (try {xs._2.maxBy(_._2)._2} catch {case _ => s})+1)))
      }
      fold[(List[Row],HashMap[J,Int])](aux,(List[Row](),HashMap[J,Int]()))
    }
    override def toString:String = toString(new IES) 
    def toString(e0:IES):String={
      val (lines,hash) = linesAndHash(e0)
      def aux2(l:Row):String={
        if (l._1._2._1 == -1)
          ""
        else if (l._2 == "App") 
          ("%3d: %29s "+MathSymbol.AlmostEqualTo+" %-29s [%3s %3s]%n").
            format(hash(l._1),l._1._1,
              l._1._3,l._2,l._1._2._1)
        else
          ("%3d: %29s "+MathSymbol.AlmostEqualTo+" %-29s [%3s %3s]%n").
            format(hash(l._1),l._1._1,
              l._1._3,l._2,l._3.
                map(x=>hash(x)).mkString(" "))
      }
      (e0.toList.sortWith((t,s)=>t._1 < s._1).map(t=>("%3d: %29s "+
      MathSymbol.AlmostEqualTo+
      " %-29s [premise]%n").
        format(t._1,t._2.lhs,t._2.rhs).mkString).
          mkString+
      lines.reverse.map(aux2 _).mkString)
    }
    def size:Int=(1 /: (subTrees.map(_.size)))(_+_)
    def toXML(e0 : IES) : scala.xml.Elem = this match {
      case REF(eq) => <refl>{eq._1.toXML}</refl>
      case SYM(eq,pt) => <sym>{pt.toXML(e0)}</sym>
      case TRA(eq,pt1,pt2) =>
        <trans>
          {pt1.toXML(e0)}
          {pt2.toXML(e0)}
        </trans>
      case APP(eq) => {
        val e = e0(eq._2._1)
        val e2 = E(eq._1,eq._3)
        val subst = if (e2.lhs matches e.lhs) e2.lhs mmatch e.lhs
                    else Subst()
        <assm>
          <rule><lhs>{e.lhs.toXML}</lhs><rhs>{e.rhs.toXML}</rhs></rule>
          {if (subst == Subst()) <substitution/>
           else {subst.toXML}}
        </assm>
      }
      case CON(eq,pts) =>
        <cong>
          <name>{eq._1.root.right.get}</name>
          {pts.map(_.toXML(e0))}
        </cong>
      //case _ => {<error>EQU should not be possible at this point</error>}
    }
  }
  //case class EQU(eq:J) extends ProofTree
  case class REF(eq:J) extends ProofTree
  case class APP(eq:J) extends ProofTree
  case class SYM(eq:J,pt:ProofTree) extends ProofTree
  case class TRA(eq:J,pt1:ProofTree,pt2:ProofTree) extends ProofTree
  case class CON(eq:J,pts:List[ProofTree]) extends ProofTree
}

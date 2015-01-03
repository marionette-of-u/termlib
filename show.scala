/** A package for fast transformation into StringBuilder, thereby facilitating
 * efficient toString. */
package object show {
  import scala.collection._
  import mutable.StringBuilder
  import scala.language.implicitConversions

  private val InitialCapacity = 128

  object ImplicitBuilder {
    implicit def emptyImplicitBuilder = new ImplicitBuilder(new StringBuilder(InitialCapacity))

    /** Every StringBuilder may be used as an ImplicitBuilder (thereby making
     * it explicit). */
    implicit def stringBuilder2ImplicitBuilder(b : StringBuilder) = new ImplicitBuilder(b)
  }

  /** If no explicit StringBuilder is given to a toStringBuilder method,
   * then by default the empty ImplicitBuilder is used. */
  class ImplicitBuilder(private val underlying : StringBuilder) {
    def append(s : String) : StringBuilder = underlying.append(s)
  }

  /** Wrapper class that allows to use toStringBuilder on any class. By
   * default toString of the underlying class is used. To increase
   * performance toStringBuilder should be customized. */
  class ToStringBuilder(a : Any) {
    def toStringBuilder(implicit b : ImplicitBuilder) = b.append(a.toString)
  }

  /** Every class may receive a call to toStringBuilder. */
  implicit def any2ToStringBuilder(a : Any) = new ToStringBuilder(a)
  
  /** A Wrapper class allowing an efficient variant of mkString on arbitrary
   * Traversable. */
  class MkStringBuilder[+A](t : Traversable[A]) {
    /** Use a function on every element of a Traversable to obtain a
     * StringBuilder.
     *
     * @param toB a function the writes the String representation of an
     * element into a (possibly implicitly) given StringBuilder
     * @param start a String to be used at the very beginning
     * @param sep   a String to be used as separator between elements
     * @param end   a String to be used at the very end. */
    def mkStringBuilder(toB : A => ImplicitBuilder => StringBuilder,
      start : String, sep : String, end : String)(implicit b : ImplicitBuilder) =
      if (t.isEmpty) b.append(start).append(end) else {
        toB(t.head)(b.append(start))
        t.tail foreach { toB(_)(b.append(sep)) }
        b.append(end)
      }
    
    /** Variant of mkStringBuilder using toStringBuilder to convert elements. */
    def mkStringBuilder(start : String, sep : String, end : String)(implicit b : ImplicitBuilder) : StringBuilder =
      mkStringBuilder(x => b => x.toStringBuilder(b), start, sep, end)

    /** Variant of mkStringBuilder where just a separator is used. */
    def mkStringBuilder(sep : String)(implicit b : ImplicitBuilder) : StringBuilder = mkStringBuilder("", sep, "")
  }
  
  /** The method mkStringBuilder may be used on every Traversable. */
  implicit def traversableLike2MkStringBuilder[A](t : Traversable[A]) = new MkStringBuilder(t)
}

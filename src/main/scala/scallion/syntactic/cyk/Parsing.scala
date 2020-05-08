package scallion.syntactic
package cyk

import scala.collection.mutable.WeakHashMap
import scala.collection.immutable.Stream.Cons
import scala.collection.immutable.Stream.Empty

/** This traint implements CYK parsing */
trait Parsing { self: Syntaxes => 
  import Syntax._

  /** Factory of parsers. */
  object CYK {

     /** Result of parsing.
      *
      * @group result
      */
    sealed trait ParseResult[A] {

      /** Parser for the rest of input. */
      val rest: Parser[A]

      /** Returns the parsed value, if any. */
      def getValue: Option[A] = this.getValues match {
        case c #:: _ => Some(c)
        case Empty => None
      }

      def getValues: Stream[A] = this match {
        case Parsed(value, _) => value
        case _ => Empty
      }
    }

    /** Indicates that the input has been fully parsed, resulting in a `value`.
      *
      * A parser for subsequent input is also provided.
      *
      * @param value The value produced.
      * @param rest  Parser for more input.
      *
      * @group result
      */
    case class Parsed[A](value: Stream[A], rest: Parser[A]) extends ParseResult[A]

    /** Indicates that the provided `token` was not expected at that point.
      *
      * The parser at the point of error is returned.
      *
      * @param token The token at fault.
      * @param rest  Parser at the point of error.
      *
      * @group result
      */
    case class UnexpectedToken[A](token: Token, rest: Parser[A]) extends ParseResult[A]

    /** Indicates that end of input was unexpectedly encountered.
      *
      * The `syntax` for subsequent input is provided.
      *
      * @param syntax Syntax at the end of input.
      *
      * @group result
      */
    case class UnexpectedEnd[A](rest: Parser[A]) extends ParseResult[A]

    sealed trait Parser[A] {
      def apply(tokens: Iterator[Token]): ParseResult[A]
    }

    private val syntaxToNetCache: WeakHashMap[Syntax[_], Net[_]] = WeakHashMap()

    def apply[A](syntax: Syntax[A]): Parser[A] = {
      var terminals: Map[Kind, Net.Elem] = Map()
      var recNets: Map[RecId, Net.Recursive[_]] = Map()
      def buildNet[B](s: Syntax[B]): Net[B] =  {
        val net: Net[B] = s match {
          case Syntax.Disjunction(left, right) => 
            Net.Disjunction[B](buildNet(left), buildNet(right))
          case Syntax.Elem(kind) => 
            if (!(terminals contains kind)) {
              terminals += (kind -> Net.Elem(kind))
            }
            terminals(kind)
          case Syntax.Failure() => Net.Failure[B]()
          case Syntax.Sequence(left, right) => Net.Sequence(buildNet(left), buildNet(right))
          case Syntax.Marked(_, inner) => buildNet(inner)
          case Syntax.Success(value, _) => Net.Epsilon[B](value)
          case Syntax.Transform(function, _, inner) => Net.Transfrom(function, buildNet(inner))
          case r: Syntax.Recursive[_] => 
            if (!(recNets contains r.id)) {
              val rec = new Net.Recursive[B] {
                override lazy val inner = syntaxToNetCache(r.inner).asInstanceOf[Net[B]]
              }
              recNets += r.id -> rec
              buildNet(r.inner)
              rec
            } else 
              recNets(r.id).asInstanceOf[Net.Recursive[B]]
        }
        syntaxToNetCache += s -> net
        net
      }
      val root = buildNet(syntax)
      NetController(root, terminals)
    }

    private case class NetController[A](root: Net[A], terminals: Map[Kind, Net.Elem]) extends Parser[A] {
      override def apply(tokens: Iterator[Token]): ParseResult[A] = {
        tokens.toStream.zipWithIndex.groupBy(_._1).mapValues(_.map{ case (t, i) => Value(t, i, i + 1) }).foreach {
          case (t, values) => terminals(getKind(t)).setValues(values)
        }
        val res = root.getValues
        if (res.isEmpty) 
          ???
        else
          Parsed(res.map(_.v), /* TODO fix */ this)
      }
    }

    private case class Value[A](v: A, start: Int, end: Int) {
      def map[B](f: A => B): Value[B] = Value(f(v), start, end)
    }

    private sealed trait Net[A] {
      def getValues: Stream[Value[A]]
    }

    private object Net {
      case class Failure[A]() extends Net[A] {
        override def getValues: Stream[Value[A]] = Empty
      }

      case class Epsilon[A](value: A) extends Net[A] {
        override def getValues: Stream[Value[A]] = Stream.from(0).map(i => Value(value, i, i))
      }

      case class Elem(kind: Kind) extends Net[Token] {
        private var values: Stream[Value[Token]] = null

        def setValues(values: Stream[Value[Token]]): Unit = this.values = values
        override def getValues: Stream[Value[Token]] = 
          if (values == null) throw new IllegalStateException("values not set")
          else values
      }

      case class Transfrom[A, B](function: A => B, inner: Net[A]) extends Net[B] {        
        override def getValues: Stream[Value[B]] = inner.getValues.map(_ map function)
      }

      case class Sequence[A, B](left: Net[A], right: Net[B]) extends Net[A ~ B] {
        override def getValues: Stream[Value[A ~ B]] = 
          // TODO optimize by using the order of the list
          for {
            a <- left.getValues
            b <- right.getValues
            if a.end == b.start
          } yield Value(a.v ~ b.v, a.start, b.end)
      }

      case class Disjunction[A](left: Net[A], right: Net[A]) extends Net[A] {
        override def getValues: Stream[Value[A]] = merge(left.getValues, right.getValues)

        private def merge(l: Stream[Value[A]], r: Stream[Value[A]]): Stream[Value[A]] =
          (l, r) match {
            case (Empty, _) => r
            case (_, Empty) => l
            case (vl #:: tl, vr #:: tr) => 
              // TODO check for ordering
              if (vl.end - vl.start > vr.end - vr.start)
                vl #:: merge(tl, r)
              else 
                vr #:: merge(l, tr)
          }
      }

      sealed abstract case class Recursive[A]() extends Net[A] {
        val inner: Net[A]

        override def getValues: Stream[Value[A]] = inner.getValues
      }

      // what about Recursive and Mark ?
    }
  }
}


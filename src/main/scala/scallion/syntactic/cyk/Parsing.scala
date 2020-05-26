package scallion.syntactic
package cyk

import scallion.util.internal.Cell
import scallion.util.internal.OptionCell
import scallion.util.internal.MergeOnceCell
import scallion.util.internal.SetCell

import scala.collection.mutable.HashMap
import scala.collection.mutable.WeakHashMap
import scala.collection.immutable.Stream.Cons
import scala.collection.immutable.Stream.Empty
import scala.language.existentials

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

    private val syntaxToNetCache: WeakHashMap[Syntax[_], Net[_, _]] = WeakHashMap()

    def apply[A](syntax: Syntax[A]): Parser[A] = {
      val recCell: HashMap[RecId, SyntaxCell[_]] = HashMap()
      def buildSyntaxCell[B](s: Syntax[B]): SyntaxCell[B] = s match {
        case Syntax.Success(value, _) => SyntaxCell.Success(value, s)
        case Syntax.Failure() => SyntaxCell.Failure(s)
        case Syntax.Elem(kind) => SyntaxCell.Elem(kind, s)
        case Syntax.Marked(mark, inner) => SyntaxCell.Marked(mark, buildSyntaxCell(inner), s)
        case Syntax.Transform(function, _, inner) => SyntaxCell.Transform(function, buildSyntaxCell(inner), s)
        case Syntax.Disjunction(left, right) => SyntaxCell.Disjunction(buildSyntaxCell(left), buildSyntaxCell(right), s)
        case Syntax.Sequence(left, right) => SyntaxCell.Sequence(buildSyntaxCell(left), buildSyntaxCell(right), s)
        case Syntax.Recursive(recId, inner) => recCell.get(recId) match {
          case Some(value) => value.asInstanceOf[SyntaxCell.Recursive[B]]
          case None => {
            val rec = SyntaxCell.Recursive(buildSyntaxCell(inner), recId, s)
            recCell += recId -> rec
            rec
          }
        }
      }

      val cell = buildSyntaxCell(syntax)

      cell.init()

      val terminals: HashMap[Kind, Net.Elem] = HashMap()
      val recNets: HashMap[RecId, Net.Recursive[_]] = HashMap()
      def buildNet[O](cell: SyntaxCell[O]): SyntaxNet[O] =  {
        val net: SyntaxNet[O] = cell match {
          case SyntaxCell.Disjunction(left, right, s) => 
            Net.Disjunction(buildNet(left), buildNet(right), cell.nullableCell.get)
          case SyntaxCell.Elem(kind, s) => 
            terminals.getOrElseUpdate(kind, Net.Elem(kind))
          case SyntaxCell.Failure(s) => 
            Net.Failure()
          case SyntaxCell.Sequence(left, right, s) => 
            Net.Sequence(buildNet(left), buildNet(right), cell.nullableCell.get)
          case SyntaxCell.Marked(_, inner, s) => 
            Net.Mark(buildNet(inner), cell.nullableCell.get)
          case SyntaxCell.Success(value, _) => 
            Net.Epsilon[O](value)
          case SyntaxCell.Transform(function, inner, s) =>
            Net.Transfrom(buildNet(inner), function, cell.nullableCell.get)
          case SyntaxCell.Recursive(inner, id, s) => 
            if (!(recNets contains id)) {
              val rec = Net.Recursive[O](syntaxToNetCache(s).asInstanceOf[Net[_, O]], cell.nullableCell.get, id)
              recNets += id -> rec
              buildNet(inner)
              rec
            } else {
              recNets(id).asInstanceOf[Net.Recursive[O]]
            }
        }
        syntaxToNetCache += cell.syntax -> net
        net
      }
      val root = buildNet(cell)
      // NetController(root, terminals.toMap)
      ???
    }

    // private case class NetController[A](root: Net[_, A], terminals: Map[Kind, Net.Elem], recs: List[Net.Recursive[_]]) extends Parser[A] {
    //   override def apply(tokens: Iterator[Token]): ParseResult[A] = {
    //     tokens.toStream.zipWithIndex.groupBy(_._1).mapValues(_.map{ case (t, i) => Value(t, i, i + 1) }).foreach {
    //       case (t, values) => terminals(getKind(t)).setValues(values)
    //     }
    //     val res = root.getValues
    //     if (res.isEmpty) 
    //       ???
    //     else
    //       Parsed(res.map(_.v), /* TODO fix */ this)
    //   }
    // }

    private case class Value[A](v: A, start: Int, end: Int) {
      def map[B](f: A => B): Value[B] = Value(f(v), start, end)
    }

    private sealed trait SyntaxCell[A] {
      def init(): Unit

      val syntax: Syntax[A]
      val nullableCell: Cell[A, A, Option[A]] = new OptionCell[A]
    }

    private object SyntaxCell {
      case class Success[A](value: A, syntax: Syntax[A]) extends SyntaxCell[A] {
        override def init(): Unit = {
          nullableCell(value)
        }
      }

      case class Failure[A](syntax: Syntax[A]) extends SyntaxCell[A] {
        override def init(): Unit = ()
      }

      case class Elem(kind: Kind, syntax: Syntax[Token]) extends SyntaxCell[Token] {
        override def init(): Unit = ()
      }

      case class Transform[A, B](function: A => B, inner: SyntaxCell[A], syntax: Syntax[B]) extends SyntaxCell[B] {
        override def init(): Unit = {
          inner.init()

          inner.nullableCell.register(nullableCell.contramap(function))
        }
      }

      case class Marked[A](mark: Mark, inner: SyntaxCell[A], syntax: Syntax[A]) extends SyntaxCell[A] {
        override def init(): Unit = {
          inner.init()

          inner.nullableCell.register(nullableCell)
        }
      }

      case class Sequence[A, B](left: SyntaxCell[A], right: SyntaxCell[B], syntax: Syntax[A ~ B]) extends SyntaxCell[A ~ B] {
        override def init(): Unit = {
          left.init()
          right.init()

          val mergeNullable: Cell[Either[A, B], (A ~ B), Option[A ~ B]] =
            new MergeOnceCell[A, B, A ~ B]((leftValue: A, rightValue: B) => leftValue ~ rightValue)

          left.nullableCell.register(mergeNullable.contramap(Left(_)))
          right.nullableCell.register(mergeNullable.contramap(Right(_)))
          mergeNullable.register(nullableCell)
        }
      }

      case class Disjunction[A](left: SyntaxCell[A], right: SyntaxCell[A], syntax: Syntax[A]) extends SyntaxCell[A] {
        override def init(): Unit = {
          left.init()
          right.init()

          left.nullableCell.register(nullableCell)
          right.nullableCell.register(nullableCell)
        }
      }

      abstract class Recursive[A] extends SyntaxCell[A] {
        def inner: SyntaxCell[A]
        val id: RecId

        var inited: Boolean = false

        override def init(): Unit = {
          if (!inited) {
            inited = true

            inner.init()

            inner.nullableCell.register(nullableCell)
          }
        }
      }

      object Recursive {
        def apply[A](cell: => SyntaxCell[A], recId: RecId, syn: Syntax[A]): SyntaxCell[A] =
          new Recursive[A] {
            override val id: RecId = recId
            override lazy val inner: SyntaxCell[A] = cell
            override val syntax: Syntax[A] = syn
          }

        def unapply[A](that: SyntaxCell[A]): Option[(SyntaxCell[A], RecId, Syntax[A])] = {
          if (that.isInstanceOf[Recursive[_]]) {
            val other = that.asInstanceOf[Recursive[A]]
            Some((other.inner, other.id, other.syntax))
          } else {
            None
          }
        }
      }
    }
    
    private type SyntaxNet[A] = Net[_, A]

    private sealed trait Net[I, O] extends (Value[I] => Unit) { self =>
      val nullable: Option[O]
      def init(): Unit
      def register(callback: Value[O] => Unit)
      def apply(value: Value[I]): Unit

      def map[P](f: O => P): Net[I, P] = new Net[I, P] {
        override val nullable: Option[P] = self.nullable.map(f)
        override def register(callback: Value[P] => Unit): Unit = self.register(v => callback(v map f))
        override def apply(value: Value[I]): Unit = self.apply(value)
      }
    }
  
    private object Net {
      case class Failure[A]() extends Net[Nothing, A] {
        override def init(): Unit = ()
        override val nullable: Option[Any] = None
        override def register(callback: Value[Any] => Unit): Unit = ()
        override def apply(value: Value[Nothing]): Unit = ()
      }

      case class Epsilon[A](value: A) extends Net[Nothing, A] {
        override def init(): Unit = ()
        override val nullable: Option[A] = Some(value)
        override def register(callback: Value[A] => Unit): Unit = ()
        override def apply(value: Value[Nothing]): Unit = ()
      }

      case class Elem(kind: Kind) extends Net[Token, Token] {
        private var registered: List[Value[Token] => Unit] = List()
        override def init(): Unit = ()
        override val nullable: Option[Value[Token]] = None
        override def register(callback: Value[Token] => Unit): Unit = {
          registered = callback :: registered
        }
        override def apply(value: Value[Token]): Unit = {
          registered.foreach(_(value))
        }
      }

      case class Transfrom[I, O](inner: Net[_, I], function: I => O, nullable: Option[O]) extends Net[I, O] {
        private var registered: List[Value[O] => Unit] = List()
        override def init(): Unit = {
          inner.register(this)
          inner.init()
        }
        override def register(callback: Value[O] => Unit): Unit = {
          registered = callback :: registered
        }
        override def apply(value: Value[I]): Unit = {
          registered.foreach(_(value map function))
        }        
      }

      case class Sequence[A, B](left: Net[_, A], right: Net[_, B], nullable: Option[A ~ B]) extends Net[Either[A, B], A ~ B] {
        private var registered: List[Value[A ~ B] => Unit] = List()
        private var fromLeft: List[Value[A]] = List()
        private var fromRight: List[Value[B]] = List()
        override def init(): Unit = {
          left.map(Left(_): Either[A, B]).register(this)
          right.map(Right(_): Either[A, B]).register(this)

          left.init()
          right.init()
        }
        override def register(callback: Value[A ~ B] => Unit): Unit = {
          registered = callback :: registered
        }        
        override def apply(value: Value[Either[A,B]]): Unit = {
          val Value(eitherV, start, end) = value
          val newValues = eitherV match {
            case Left(v) => {
              fromLeft = Value(v, start, end) :: fromLeft
              val combinedWithRight = fromRight.filter(_.start == end).map {
                  case Value(v1, _, end1) => Value(v ~ v1, start, end1)
                }
              if (right.nullable.isEmpty)
                combinedWithRight
              else 
                Value(v ~ right.nullable.get, start, end)::combinedWithRight
            }
            case Right(v) => {
              fromRight = Value(v, start, end) :: fromRight
              val combinedWithLeft = fromLeft.filter(_.end == start).map {
                  case Value(v1, _, end1) => Value(v1 ~ v, start, end1)
                }
              if (right.nullable.isEmpty)
                combinedWithLeft
              else 
                Value(left.nullable.get ~ v, start, end)::combinedWithLeft
            }
          }
          // TODO fix the following for only one value 
          registered.foreach(c => newValues foreach(c(_)))
        }
      }

      case class Disjunction[A](left: Net[_, A], right: Net[_, A], nullable: Option[A]) extends Net[A, A] {
        private var registered: List[Value[A] => Unit] = List()
        override def init(): Unit = {
          right.register(this)
          left.register(this)
          
          right.init()
          left.init()
        }
        override def register(callback: Value[A] => Unit): Unit = {
          registered = callback :: registered
        }
        override def apply(value: Value[A]): Unit = {
          registered.foreach(_(value))
        }
      }

      case class Mark[A](inner: Net[_, A], nullable: Option[A]) extends Net[A, A] {
        private var registered: List[Value[A] => Unit] = List()
        override def init(): Unit = {
          inner.register(this)
          inner.init()
        }
        override def register(callback: Value[A] => Unit): Unit = {
          registered = callback :: registered
        }
        override def apply(value: Value[A]): Unit = {
          registered.foreach(_(value))
        }
      }

      abstract class Recursive[A] extends Net[A, A] {
        private var registered: List[Value[A] => Unit] = List()
        private val values: HashMap[Int, HashMap[Int, A]] = HashMap()
        private var initialized = false
        val id: RecId
        val inner: Net[_, A]
        override def init(): Unit = {
          if (!initialized) {
            initialized = true
            inner.register(this)
            inner.init()
          }
        }
        override def register(callback: Value[A] => Unit): Unit = {
          registered = callback :: registered
        }
        override def apply(value: Value[A]): Unit = {
          if (!(values.contains(value.start) && values(value.start).contains(value.end))) {
            values.getOrElseUpdate(value.start, HashMap((value.end, value.v)))
            registered.foreach(_(value))
          }
        }
      }
      object Recursive {
        def apply[A](inner: => Net[_, A], nullableOpt: Option[A], recId: RecId): Net.Recursive[A] = {
          new Net.Recursive[A] {
            override lazy val inner: Net[_, A] = inner
            override val nullable: Option[A] = nullableOpt
            override val id: RecId = recId
          }
        }
        def unapply[A](that: Net.Recursive[A]): Option[(Net[_, A], Option[A], RecId)] = {
          if (that.isInstanceOf[Net.Recursive[A]]) {
            val other = that.asInstanceOf[Net.Recursive[A]]
            Some((other.inner, other.nullable, other.id))
          } else {
            None
          }
        }
      }
    }
  }
}


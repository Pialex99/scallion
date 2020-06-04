package scallion.syntactic
package cyk

import scallion.util.internal.Cell
import scallion.util.internal.BooleanCell
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
      def getValue: Option[A] = this match {
        case Parsed(v, _) => Some(v)
        case _ => None
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
    case class Parsed[A](value: A, rest: Parser[A]) extends ParseResult[A]

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

    private val syntaxToNetCache: WeakHashMap[Syntax[_], SyntaxNet[_]] = WeakHashMap()

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

      val terminals: HashMap[Kind, SyntaxNet.Elem] = HashMap()
      val recNets: HashMap[RecId, SyntaxNet.Recursive[_]] = HashMap()
      def buildNet[O](cell: SyntaxCell[O]): SyntaxNet[O] = {
        val net: SyntaxNet[O] = cell match {
          case SyntaxCell.Disjunction(left, right, _) => 
            // if the left and the right are not productives then the all syntax would not be productive so we should not be here
            if (!left.productiveCell.get) {
              assert(right.productiveCell.get)
              buildNet(right)
            } else if (!right.productiveCell.get) {
              assert(left.productiveCell.get)
              buildNet(left)
            } else 
              SyntaxNet.Disjunction(buildNet(left), buildNet(right), cell.nullableCell.get)
          case SyntaxCell.Elem(kind, _) => 
            terminals.getOrElseUpdate(kind, SyntaxNet.Elem(kind))
          case SyntaxCell.Failure(_) => 
            SyntaxNet.Failure()
          case SyntaxCell.Sequence(left, right, _) => 
            SyntaxNet.Sequence(buildNet(left), buildNet(right), cell.nullableCell.get)
          case SyntaxCell.Marked(_, inner, _) => 
            SyntaxNet.Mark(buildNet(inner), cell.nullableCell.get)
          case SyntaxCell.Success(value, _) => 
            SyntaxNet.Epsilon[O](value)
          case SyntaxCell.Transform(function, inner, _) =>
            SyntaxNet.Transfrom(buildNet(inner), function, cell.nullableCell.get)
          case SyntaxCell.Recursive(inner, id, _) => 
            if (!(recNets contains id)) {
              val rec = SyntaxNet.Recursive[O](syntaxToNetCache(inner.syntax).asInstanceOf[SyntaxNet[O]], cell.nullableCell.get, id)
              recNets += id -> rec
              buildNet(inner)
              rec
            } else {
              recNets(id).asInstanceOf[SyntaxNet.Recursive[O]]
            }
        }
        syntaxToNetCache += cell.syntax -> net
        net
      }

      val root = buildNet(cell)
      root.init()
      NetController(root, terminals.toMap, 0)
    }

    private case class NetController[A](root: SyntaxNet[A], terminals: Map[Kind, SyntaxNet.Elem], startingIndex: Int) extends Parser[A] {
      override def apply(tokens: Iterator[Token]): ParseResult[A] = {
        var index = startingIndex
        val workingRoot = 
        while (tokens.hasNext) {
          val token = tokens.next()
          if (!terminals.contains(getKind(token)))
            return UnexpectedToken(token, this)
          terminals(getKind(token)).net.apply(Value(token, index, index + 1))
          index += 1
        }
        val res = if (index == 0) root.nullable else root.net.get(0, index)
        res match {
          case Some(value) => Parsed(value, this)
          case None => UnexpectedEnd(this)
        }
      }
    }

    private sealed trait SyntaxCell[A] {
      def init(): Unit

      val syntax: Syntax[A]
      val nullableCell: Cell[A, A, Option[A]] = new OptionCell[A]
      val productiveCell: Cell[Unit, Unit, Boolean] = new BooleanCell
    }

    private object SyntaxCell {
      case class Success[A](value: A, syntax: Syntax[A]) extends SyntaxCell[A] {
        override def init(): Unit = {
          nullableCell(value)
          productiveCell(())
        }
      }

      case class Failure[A](syntax: Syntax[A]) extends SyntaxCell[A] {
        override def init(): Unit = ()
      }

      case class Elem(kind: Kind, syntax: Syntax[Token]) extends SyntaxCell[Token] {
        override def init(): Unit = {
          productiveCell(())
        }
      }

      case class Transform[A, B](function: A => B, inner: SyntaxCell[A], syntax: Syntax[B]) extends SyntaxCell[B] {
        override def init(): Unit = {
          inner.init()

          inner.nullableCell.register(nullableCell.contramap(function))
          inner.productiveCell.register(productiveCell)
        }
      }

      case class Marked[A](mark: Mark, inner: SyntaxCell[A], syntax: Syntax[A]) extends SyntaxCell[A] {
        override def init(): Unit = {
          inner.init()

          inner.nullableCell.register(nullableCell)
          inner.productiveCell.register(productiveCell)
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

          val mergeProductive: Cell[Either[Unit, Unit], Unit, Option[Unit]] =
            new MergeOnceCell[Unit, Unit, Unit]((_, _) => ())

          left.productiveCell.register(mergeProductive.contramap(Left(_)))
          right.productiveCell.register(mergeProductive.contramap(Right(_)))
          mergeProductive.register(productiveCell)
        }
      }

      case class Disjunction[A](left: SyntaxCell[A], right: SyntaxCell[A], syntax: Syntax[A]) extends SyntaxCell[A] {
        override def init(): Unit = {
          left.init()
          right.init()

          left.nullableCell.register(nullableCell)
          right.nullableCell.register(nullableCell)

          left.productiveCell.register(productiveCell)
          right.productiveCell.register(productiveCell)
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

            inner.productiveCell.register(productiveCell)
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

    private case class Value[+A](v: A, start: Int, end: Int) {
      def map[B](f: A => B): Value[B] = Value(f(v), start, end)
    }

    private class Net[A] extends Cell[Value[A], Value[A], (Int, Int) => Option[A]] { self =>
      private var registered: List[Value[A] => Unit] = List()
      private val values: HashMap[(Int, Int), A] = HashMap()
      override def register(callback: Value[A] => Unit) = {
        registered = callback :: registered
      }
      override def apply(value: Value[A]) = value match {
        case Value(v, start, end) =>
          if (!values.contains((start, end))) {
            values += (start, end) -> v
            registered.foreach(_(value))
          }
      }
      override def get: (Int, Int) => Option[A] = (s, e) => values.get((s, e))
    }

    private class MergeNet[A, B](nullableLeft: Option[A], nullableRight: Option[B]) extends Cell[Either[Value[A], Value[B]], Value[A ~ B], (Int, Int) => Option[A ~ B]] {
      private var registered: List[Value[A ~ B] => Unit] = List()
      private val values: HashMap[(Int, Int), A ~ B] = HashMap()

      private val fromLeft: HashMap[Int, HashMap[Int, A]] = HashMap()
      private val fromRight: HashMap[Int, HashMap[Int, B]] = HashMap()

      override def register(callback: Value[A ~ B] => Unit) = {
        registered = callback :: registered
      }
      override def apply(value: Either[Value[A], Value[B]]) = value match {
        case Right(Value(v, start, end)) =>
          if (!(fromRight.contains(start) && fromRight(start).contains(end))) {
            fromRight.getOrElseUpdate(start, HashMap()) += end -> v
            if (nullableLeft.isDefined && !values.contains((start, end))) {
              values += (start, end) -> nullableLeft.get ~ v
              registered.foreach(_(Value(nullableLeft.get ~ v, start, end)))
            }
            if (fromLeft contains start) {
              for ((s, va) <- fromLeft(start)) {
                registered.foreach(_(Value(va ~ v, s, end)))
              }
            }
          }
        case Left(Value(v, start, end)) => 
          if (!(fromLeft.contains(end) && fromLeft(end).contains(start))) {
            fromLeft.getOrElseUpdate(end, HashMap()) += start -> v
            if (nullableRight.isDefined && !values.contains((start, end))) {
              values += (start, end) -> v ~ nullableRight.get
              registered.foreach(_(Value(v ~ nullableRight.get, start, end)))
            }
            if (fromRight contains end) {
              for ((e, vb) <- fromRight(end)) {
                registered.foreach(_(Value(v ~ vb, start, e)))
              }
            }
          }
      }
      override def get: (Int, Int) => Option[A ~ B] = (s, e) => values.get((s, e))
    }
    
    private sealed trait SyntaxNet[A] {
      val net: Cell[Value[A], Value[A], (Int, Int) => Option[A]] = new Net[A]
      val nullable: Option[A]
      def init(): Unit
      // def copy(): SyntaxNet[A]
    }
  
    private object SyntaxNet {
      case class Failure[A]() extends SyntaxNet[A] {
        override val nullable: Option[A] = None
        override def init(): Unit = ()
        // override def copy(): SyntaxNet[A] = Failure[A]()
      }

      case class Epsilon[A](value: A) extends SyntaxNet[A] {
        override val nullable: Option[A] = Some(value)
        override def init(): Unit = ()
        // override def copy(): SyntaxNet[A] = Epsilon(value)
      }

      case class Elem(kind: Kind) extends SyntaxNet[Token] {
        override val nullable: Option[Token] = None
        override def init(): Unit = ()
        // override def copy(): SyntaxNet[Token] = Elem(kind)
      }

      case class Transfrom[I, O](inner: SyntaxNet[I], function: I => O, nullable: Option[O]) extends SyntaxNet[O] {
        override def init(): Unit = {
          inner.init()
          
          inner.net.map((v: Value[I]) => v map function).register(this.net)
        }
      }

      case class Sequence[A, B](left: SyntaxNet[A], right: SyntaxNet[B], nullable: Option[A ~ B]) extends SyntaxNet[A ~ B] {
        override def init(): Unit = {
          left.init()
          right.init()
          
          val mergeNet = new MergeNet(left.nullable, right.nullable)
          mergeNet.register(this.net)

          left.net.map(Left(_)).register(mergeNet)
          right.net.map(Right(_)).register(mergeNet)
        }
      }

      case class Disjunction[A](left: SyntaxNet[A], right: SyntaxNet[A], nullable: Option[A]) extends SyntaxNet[A] {
        override def init(): Unit = {
          left.init()
          right.init()

          left.net.register(this.net)
          right.net.register(this.net)
        }
      }

      case class Mark[A](inner: SyntaxNet[A], nullable: Option[A]) extends SyntaxNet[A] {
        override def init(): Unit = {
          inner.init()

          inner.net.register(this.net)
        }
      }

      abstract class Recursive[A] extends SyntaxNet[A] {
        private var initialized = false
        val id: RecId
        val inner: SyntaxNet[A]
        override def init(): Unit = {
          if (!initialized) {
            initialized = true
            inner.init()

            inner.net.register(this.net)
          }
        }
      }
      object Recursive {
        def apply[A](innerNet: => SyntaxNet[A], nullableOpt: Option[A], recId: RecId): Recursive[A] = {
          new Recursive[A] {
            override lazy val inner: SyntaxNet[A] = innerNet
            override val nullable: Option[A] = nullableOpt
            override val id: RecId = recId
          }
        }
        def unapply[A](that: Recursive[A]): Option[(SyntaxNet[A], Option[A], RecId)] = {
          if (that.isInstanceOf[Recursive[A]]) {
            val other = that.asInstanceOf[Recursive[A]]
            Some((other.inner, other.nullable, other.id))
          } else {
            None
          }
        }
      }
    }
  }
}


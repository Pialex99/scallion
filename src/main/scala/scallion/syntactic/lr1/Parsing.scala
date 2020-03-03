package scallion.syntactic
package lr1

import scallion.util.internal._
import scallion.syntactic._
import scala.collection.mutable.Queue

/** This trait implements LR(1) parsing. */
trait LR1Parsing extends Parsing { self: Syntaxes =>
  import Syntax._
  /** Factory of LR(1) parsers. */
  object LR1 extends ParserFactory {

    /** Contains the description of the various LR(1) conflicts.
      *
      * @group conflict
      */
    object LR1Conflict {
    }

    /** 
     * Contains the definitions and the function used to convert a syntax into a set of rules
     */
    object grammar {
      /** 
       * Used to indentify non-terminal symbols 
      */
      type Id = Int
      
      /**
        * A symbol in a rule
        */
      sealed trait Symbol[A] 

      /**
        * The epsilon symbol
        *
        * @param value the value associated with it
        */
      case class Epsilon[A](value: A) extends Symbol[A]
      /**
        * A terminal symbol
        *
        * @param kind the token kind that this terminal accepts
        */
      case class Terminal(kind: Kind) extends Symbol[Token]
      /**
        * A non-terminal symbol
        *
        * @param id the id used to identify this non-terminal
        */
      case class NonTerminal[A](id: Id) extends Symbol[A]

      /**
        * A trait for a grammar production rule
        */
      sealed trait Rule[A] { 
        /**
          * the id of the non-terminal this rules is associated with
          */
        val ntId: Id 
      }
      /**
        * A rule used to apply a transformation when reducing, it can only be applied to a single non-terminal
        *
        * @param ntId   the id of the non-terminal associated with this rule
        * @param f      the mapping function to apply when reducing
        * @param symbol the source symbol
        */
      case class TransformRule[A, B](ntId: Id, f: B => A, symbol: Symbol[B]) extends Rule[A]
      /**
        * A normal rule without transformation
        *
        * @param ntId    the id of the non-terminal associated with this rule
        * @param symbols the sequence of symbols that the non-terminal expands to 
        */
      case class NormalRule0[A](ntId: Id, value: A) extends Rule[A]
      case class NormalRule1[A](ntId: Id, symbol0: Symbol[A]) extends Rule[A]
      case class NormalRule2[A, B](ntId: Id, symbol0: Symbol[A], symbol1: Symbol[B]) extends Rule[A~B]
      // case class NormalRule3[A, B, C](ntId: Id, symbol0: Symbol[A], symbol1: Symbol[B], symbol2: Symbol[C]) extends Rule[A~B~C]
      // case class NormalRule4[A, B, C, D](ntId: Id, symbol0: Symbol[A], symbol1: Symbol[B], symbol2: Symbol[C], symbol3: Symbol[D]) extends Rule[A~B~C~D]
      // case class NormalRule5[A, B, C, D, E](ntId: Id, symbol0: Symbol[A], symbol1: Symbol[B], symbol2: Symbol[C], symbol3: Symbol[D], symbol4: Symbol[E]) extends Rule[A~B~C~D~E]
      // case class NormalRule6[A, B, C, D, E, F](ntId: Id, symbol0: Symbol[A], symbol1: Symbol[B], symbol2: Symbol[C], symbol3: Symbol[D], symbol4: Symbol[E], symbol5: Symbol[F]) extends Rule[A~B~C~D~E~F]
      // case class NormalRule7[A, B, C, D, E, F, G](ntId: Id, symbol0: Symbol[A], symbol1: Symbol[B], symbol2: Symbol[C], symbol3: Symbol[D], symbol4: Symbol[E], symbol5: Symbol[F], symbol6: Symbol[G]) extends Rule[A~B~C~D~E~F~G]
      // case class NormalRule8[A, B, C, D, E, F, G, H](ntId: Id, symbol0: Symbol[A], symbol1: Symbol[B], symbol2: Symbol[C], symbol3: Symbol[D], symbol4: Symbol[E], symbol5: Symbol[F], symbol6: Symbol[G], symbol7: Symbol[H]) extends Rule[A~B~C~D~E~F~G~H]
      // case class NormalRule9[A, B, C, D, E, F, G, H, I](ntId: Id, symbol0: Symbol[A], symbol1: Symbol[B], symbol2: Symbol[C], symbol3: Symbol[D], symbol4: Symbol[E], symbol5: Symbol[F], symbol6: Symbol[G], symbol7: Symbol[H], symbol8: Symbol[I]) extends Rule[A~B~C~D~E~F~G~H~I]
      // case class NormalRule10[A, B, C, D, E, F, G, H, I, J](ntId: Id, symbol0: Symbol[A], symbol1: Symbol[B], symbol2: Symbol[C], symbol3: Symbol[D], symbol4: Symbol[E], symbol5: Symbol[F], symbol6: Symbol[G], symbol7: Symbol[H], symbol8: Symbol[I], symbol9: Symbol[J]) extends Rule[A~B~C~D~E~F~G~H~I~J]
      /**
        * A rule for the `Failure` syntax
        */
      case class FailureRule[A](ntId: Id) extends Rule[A]

      /**
        * Transform a `Syntax` into a sequence of rules
        *
        * @param syntax the syntax to transform
        * @return       the sequence of rules
        * 
        * @note inspired form scallion.syntactic.visualization.Grammars
        */
      def getRules[A](syntax: Syntax[A]) = {
        var nextId: Id = 1
        var rules = Vector[Rule[_]]()
        val queue = new Queue[Syntax[_]]
        var ids = Map[Syntax[_], Id]()

        def idOf[B](next: Syntax[B]): Id = 
          if (!ids.contains(next)) {
            val res = nextId
            nextId += 1
            ids += next -> res
            res
          } else {
            ids(next)
          }
        
        def symbolOf[B](next: Syntax[B]): Symbol[B] = next match {
          case Elem(kind) => 
            Terminal(kind)
          case _ => 
            if (!ids.contains(next))
              queue.enqueue(next)
            val id = idOf(next)
            NonTerminal(id)
        }

        def getRuleSeq[B](id: Id, s: Syntax[B]): Seq[Rule[_]] = s match {
          case Disjunction(left, right) => 
            getRuleSeq(id, left) ++ getRuleSeq(id, right)
          case Sequence(left, right) => 
            val s1 = symbolOf(left)
            val s2 = symbolOf(right)
            Seq(NormalRule2(id, s1, s2))
          case Elem(kind) => 
            Seq(NormalRule1(id, Terminal(kind)))
          case Failure() => 
            Seq(FailureRule(id))
          case r: Recursive[_] => 
            val s1 = symbolOf(r.inner)
            Seq(NormalRule1(id, s1))
          case Transform(f, _, inner) => 
            val id1 = idOf(s)
            val s1 = symbolOf(inner)
            (if (id1 == id) Seq() else Seq(NormalRule1(id, NonTerminal(id1)))) :+ TransformRule(id1, f, s1)
          case Success(value, _) => 
            Seq(NormalRule0(id, value))
        }

        val s0 = symbolOf(syntax)
        rules :+= NormalRule1(0, s0)

        while (queue.nonEmpty) {
          val current = queue.dequeue()
          import scala.language.existentials
          rules ++= getRuleSeq(idOf(current), current)
        }
        rules
      }
    }

    import grammar._

    object item {
      type State = Int
      sealed trait Action 
      case class Shift(nextState: State) extends Action
      case class Reduce(rule: Rule[_]) extends Action
      case object Done extends Action

      type ItemSet = Seq[Item]
      case class Item(id: Id, prefix: Seq[Symbol[_]], postfix: Seq[Symbol[_]]) {
        def startWith: Option[Symbol[_]] = postfix.headOption

        def shift:Option[Item] = startWith.map(s => Item(id, prefix :+ s, postfix.tail))
      }
      def items[A](rule: Rule[_]) = ??? // rule match {
      //   case NormalRule(id, symbols) => 
      //     (symbols.inits.toList.reverse, symbols.tails.toList).zipped.map((xs, ys) => Item(id, xs, ys)).toSet
      //   case TransformRule(id, f, symbol) => 
      //     Set(Item(id, Seq(symbol), Seq()), Item(id, Seq(), Seq(symbol)))
      // }

      def close(itemSet: ItemSet, allItems: Seq[Item]): ItemSet = {
        val queue = new Queue[Item]()
        var closedSet = itemSet
        itemSet.foreach(queue.enqueue(_))
        while (!queue.isEmpty) {
          val i = queue.dequeue()
          i.startWith match {
            case None => ()
            case Some(Terminal(_)) => ()
            case Some(Epsilon(_)) => ???
            case Some(NonTerminal(id)) => 
              val toAdd = allItems.filter(i2 => i2.id == id && i2.prefix.isEmpty).diff(closedSet)
              toAdd.foreach(queue.enqueue(_))
              closedSet ++= toAdd
          }
        }
        closedSet
      }

      def startWith(itemSet: ItemSet): Set[Symbol[_]] = itemSet.flatMap(_.startWith).toSet

      def generateTransitionTable(itemSet0: ItemSet, allItems: Seq[Item]): Map[Int, Map[Symbol[_], Int]] = {
        var nextId = 1
        val queue = new Queue[ItemSet]()
        var res: Map[Int, Map[Symbol[_], Int]] = Map()
        var ids: Map[ItemSet, Int] = Map(itemSet0 -> 0)
        queue.enqueue(itemSet0)
        while (!queue.isEmpty) {
          val is = queue.dequeue()
          res = res + (ids(is) -> startWith(is).map (x => {
            val s = close(is.filter(_.startWith == Some(x)).flatMap(_.shift), allItems)
            val id = 
              if (ids contains s) 
                ids(s)
              else {
                val newId = nextId
                nextId += 1
                queue.enqueue(s)
                ids += s -> newId
                newId
              }
            x -> id
          }).toMap)
        }
        res
      }
    }

    import item._

    /** Builds a LR(1) parser from a syntax description.
      *
      * @param syntax     The description of the syntax.
      * @param enforceLL1 Indicates if the method should throw a
      *                   `ConflictException` when the `syntax` is not LR(1).
      *                   `true` by default.
      * @throws ConflictException when the `syntax` is not LR(1) and `enforceLR1` is not set to `false`.
      * @group parsing
      */
    override def apply[A](syntax: Syntax[A], enforceLR1: Boolean = true): LR1Parser[A] = {
      val rules = getRules(syntax)
      rules.foreach(println)
      ???
      val allItems = rules.flatMap(items)
      val itemSet0 = close(Seq(allItems.head), allItems)
      val transitionTable = generateTransitionTable(itemSet0, allItems)
      transitionTable.foreach(println)
      ???
    }
    
    type State = Int

    object stack {
      sealed trait CombinedElems[A]

      case class Single[A](value: A) extends CombinedElems[A]
      case class Tuple[A, B](value:A, rest:CombinedElems[B]) extends CombinedElems[A ~ B]

      sealed trait Stack[A] {
        val state: State
        def combine(n: Int): Option[CombinedElems[A]]
      }

      case class EmptyStack[A]() extends Stack[A] { 
        val state = 0
        override def combine(n: Int): Option[CombinedElems[A]] = None
      }

      case class ConsStack[A, B](
        head: StackElem[A],
        tail: Stack[B]
      ) extends Stack[A ~ B] { 
        val state = head.state
        override def combine(n: Int): Option[CombinedElems[A ~ B]] = ???
          // if (n == 1)
          //   Some(Single(head.value))
          // else
          //   combine(n - 1) map ()
      }

      case class StackElem[A](state: State, value: A, symbol: Symbol[A])
    }

    import stack._

    class LR1Parser[A](actionTable: Vector[Map[Kind, Action]], endTable: Vector[Action], gotoTable: Vector[Map[Id, State]]) extends Parser[A] {

      private def getState(stack: List[StackElem[_]]): State = stack match {
        case Nil => 0
        case StackElem(state, _, _) :: _ => state
      }

      private def getAction(state: State, token: Token): Option[Action] = actionTable(state).get(getKind(token))

      private def applyAction(stack: List[StackElem[_]], action: Option[Action], t: Token): Either[ParseResult[A], List[StackElem[_]]] = ??? //action match {
      //   case None => Left(UnexpectedToken(t, actionTable(getState(stack)).keySet, this))
      //   case Some(Done) => throw new RuntimeException("Table not correct")
      //   case Some(Shift(nextState)) => Right(StackElem(nextState, t, Terminal(getKind(t)))::stack)
      //   case Some(Reduce(r@NormalRule1(ntId, symbols))) => 
      //     val (elems, newStack) = stack.splitAt(symbols.size)
      //     val newState = gotoTable(getState(newStack))(ntId)
      //     def combine(xs0: List[_]): _~_ = xs0 match {
      //       case Nil => throw new RuntimeException("Unexpected Nil found")
      //       case x0 :: x1 :: Nil => x1 ~ x0
      //       case x :: xs => combine(xs) ~ x
      //     }
      //     val combinedElems = ???//combine(elems).asInstanceOf[r.wtt.type]
      //     applyAction(StackElem(newState, combinedElems, NonTerminal(ntId)) :: newStack, getAction(newState, t), t)
      //   case Some(Reduce(r@TransformRule(ntId, f, _))) => 
      //     val (h::tail) = stack
      //     ???
      // }

      override def apply(tokens: Iterator[Token]): ParseResult[A] = {
        var stack: List[StackElem[_]] = List()
        while (tokens.hasNext) {
          val t = tokens.next()
          val tk = getKind(t)
          val s = getState(stack)
          val action = getAction(s, t) 
          applyAction(stack, action, t) match {
            case Left(value) => 
              return value
            case Right(value) => 
              stack = value
          }
        }

        ???
      }
    }
  }
}

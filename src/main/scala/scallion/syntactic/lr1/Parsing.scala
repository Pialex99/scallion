package scallion.syntactic
package lr1

import scallion.util.internal._
import scallion.syntactic._
import scala.collection.mutable.Queue
import scala.reflect.runtime.universe._

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

    object grammar {
      type Id = Int
      
      sealed trait Symbol[A] {
        val wtt: WeakTypeTag[A] = weakTypeTag[A]
      } 

      case class Epsilon[A](value: A) extends Symbol[A]
      case class Terminal(kind: Kind) extends Symbol[Token]
      case class NonTerminal[A](id: Id) extends Symbol[A]

      sealed trait Rule[A] { 
        val ntId: Id 
        val wtt: WeakTypeTag[A] = weakTypeTag[A]
      }
      case class TransformRule[A, B](ntId: Id, f: B => A, symbol: NonTerminal[B]) extends Rule[A]
      case class NormalRule[A](ntId: Id, symbols: Seq[Symbol[_]]) extends Rule[A]
      
      type State = Int
    
      sealed trait Action 
      case class Shift(nextState: State) extends Action
      case class Reduce(rule: Rule[_]) extends Action
      case object Done extends Action

      def getRules[A](syntax: Syntax[A]) = {
        var nextId: Id = 1
        var rules = Vector[Rule[_]]()
        val queue = new Queue[Syntax[_]]
        var ids = Map[Syntax[_], Id]()

        def inspect[B](next: Syntax[B]): Id = {
          if (!ids.contains(next)) {
            val res = nextId
            nextId += 1
            ids += next -> res
            queue.enqueue(next)
            res
          }
          else {
            ids(next)
          }
        }
        def getSymbols[B](next: Syntax[B]): Seq[Seq[Symbol[_]]] = next match {
          case Disjunction(left, right) => getSymbols(left) ++ getSymbols(right)
          case _ => Seq(getSequents(next))
        }
        def getSequents[B](next: Syntax[B]): Seq[Symbol[_]] = next match {
          case Failure() => Seq()
          case Success(value, _) => Seq(Epsilon(value))
          case Elem(kind) => Seq(Terminal(kind))
          case t@Transform(_, _, _) => {
            val id = inspect(t)
            Seq(NonTerminal(id))
          }
          case Sequence(left, right) => getSequents(left) ++ getSequents(right)
          case d@Disjunction(_, _) => {
            val id = inspect(d)
            Seq(NonTerminal(id))
          }
          case Recursive(_, inner) => {
            val id = inspect(inner)
            Seq(NonTerminal(id))
          }
        }

        inspect(syntax)
        rules :+= NormalRule(0, Seq(NonTerminal(ids(syntax))))

        while (queue.nonEmpty) {
          val current = queue.dequeue()
          rules ++= (current match {
            case Transform(f, _, inner) => Seq(TransformRule(ids(current), f, NonTerminal(inspect(inner))))
            case _ => getSymbols(current).map(NormalRule(ids(current), _))
          })
        }
        rules
      }
    }

    import grammar._

    object item {

      type ItemSet = Seq[Item]
      case class Item(id: Id, prefix: Seq[Symbol[_]], postfix: Seq[Symbol[_]]) {
        def startWith: Option[Symbol[_]] = postfix.headOption

        def shift:Option[Item] = startWith.map(s => Item(id, prefix :+ s, postfix.tail))
      }
      def items[A](rule: Rule[_]) = rule match {
        case NormalRule(id, symbols) => 
          (symbols.inits.toList.reverse, symbols.tails.toList).zipped.map((xs, ys) => Item(id, xs, ys)).toSet
        case TransformRule(id, f, symbol) => 
          Set(Item(id, Seq(symbol), Seq()), Item(id, Seq(), Seq(symbol)))
      }

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
      val allItems = rules.flatMap(items)
      val itemSet0 = close(Seq(allItems.head), allItems)
      val transitionTable = generateTransitionTable(itemSet0, allItems)
      transitionTable.foreach(println)
      ???
    }
    
    type State = Int

    case class StackElem[A](state: State, value: A, symbol: Symbol[A]) {
      val wtt = weakTypeTag[A] 
    }
    class LR1Parser[A](actionTable: Array[Map[Kind, Action]], endTable: Array[Action], gotoTable: Array[Map[Id, State]]) extends Parser[A] {

      private def getState(stack: List[StackElem[_]]): State = stack match {
        case Nil => 0
        case StackElem(state, _, _) :: _ => state
      }

      private def getAction(state: State, token: Token): Option[Action] = actionTable(state).get(getKind(token))

      private def applyAction(stack: List[StackElem[_]], action: Option[Action], t: Token): Either[ParseResult[A], List[StackElem[_]]] = action match {
        case None => Left(UnexpectedToken(t, actionTable(getState(stack)).keySet, this))
        case Some(Done) => throw new RuntimeException("Table not correct")
        case Some(Shift(nextState)) => Right(StackElem(nextState, t, Terminal(getKind(t)))::stack)
        case Some(Reduce(NormalRule(ntId, symbols))) => 
          val (elems, newStack) = stack.splitAt(symbols.size)
          val newState = gotoTable(getState(newStack))(ntId)
          val combinedElems = ???
          applyAction(StackElem(newState, combinedElems, NonTerminal(ntId)) :: newStack, getAction(newState, t), t)
        case Some(Reduce(r@TransformRule(ntId, f, _))) => ???
      }

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

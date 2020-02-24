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

      case class Terminal(kind: Kind) extends Symbol[Token]
      case class Epsilon[A](value: A) extends Symbol[A]
      case class NonTerminal[A](id: Id) extends Symbol[A]

      sealed trait Rule[A] { val id: Id }
      case class TransformRule[A, B](id: Id, f: B => A, symbol: NonTerminal[B]) extends Rule[A]
      case class NormalRule[A](id: Id, symbols: Seq[Symbol[_]]) extends Rule[A]
      
      type State = Int
    
      sealed trait Action 
      case class Shift(nextState: State) extends Action
      case class Reduce(rule: Rule[_]) extends Action
      case object Done extends Action

      def getRules[A](syntax: Syntax[A]) = {
        var nextId: Id = 0
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
        while (queue.nonEmpty) {
          val current = queue.dequeue()
          rules ++= (current match {
            case Transform(f, _, inner) => Seq(TransformRule(ids(current), f, NonTerminal(inspect(inner))))
            case _ => getSymbols(current).map(NormalRule(ids(current), _))
          })
        }
        rules
      }

      case class Item(id: Id, prefix: Seq[Symbol[_]], postfix: Seq[Symbol[_]])
      def items[A](rule: Rule[A]) = rule match {
        case NormalRule(id, symbols) => ???// symbols.inits.zip(symbols.tails).map(Item(id, _._1, _._2))
        case TransformRule(id, f, symbol) => ???
      }
    }

    import grammar._


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

      // def findDisjunctionTransformAndRecurvise[T](s: Syntax[T], acc: Map[Syntax[_], Id], lastId: Id): (Map[Syntax[_], Id], Id) = 
      //   if (acc contains s) (acc, lastId) else s match {
      //   case Failure() => (acc, lastId)
      //   case Elem(_) => (acc, lastId)
      //   case Success(_, _) => (acc, lastId)
      //   case Transform(_, _, inner) => 
      //     findDisjunctionTransformAndRecurvise(inner, acc + (s -> lastId), lastId + 1)
      //   case Sequence(left, right) => 
      //     val (leftresult, leftLastId) = findDisjunctionTransformAndRecurvise(left, acc, lastId)
      //     findDisjunctionTransformAndRecurvise(right, leftresult, leftLastId)
      //   case Disjunction(left, right) =>
      //     val (leftresult, leftLastId) = findDisjunctionTransformAndRecurvise(left, acc + (s -> lastId), lastId + 1)
      //     findDisjunctionTransformAndRecurvise(right, leftresult, leftLastId)
      //   case r: Recursive[_] => 
      //     findDisjunctionTransformAndRecurvise(r.inner, acc + (r -> lastId), lastId + 1)
      // }
      // val (nonTerminals, lastId) = findDisjunctionTransformAndRecurvise(syntax, Map(), 0)
      // println(nonTerminals mkString "\n\n")
      // println(nonTerminals.size, lastId)
      // val properNonTermials: Set[NonTerminal[_]] = nonTerminals.map{case (s:Syntax[_], id) => NonTerminal(s, id)}.toSet
      // ???
    }
    
    sealed trait LR1Parser[A] extends Parser[A] {
      override def apply(tokens: Iterator[Token]): ParseResult[A] = ???
      
    }
  }
}

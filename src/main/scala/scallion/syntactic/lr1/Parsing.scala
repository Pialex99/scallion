package scallion.syntactic
package lr1

import scallion.util.internal._
import scallion.syntactic._
import scala.collection.mutable.Queue
import scala.annotation.tailrec
import scala.collection.mutable.HashMap
import scala.collection.immutable.IntMap

/** This trait implements LR(1) parsing. */
trait Parsing { self: Syntaxes =>
  import Syntax._
  /** Factory of LR(1) parsers. */
  object LR1 {

    /** Describes a LR(1) conflict.
      *
      * @group conflict
      */
    sealed trait Conflict

    /** Contains the description of the various LR(1) conflicts.
      *
      * @group conflict
      */
    object Conflict {
      case class ReduceReduce(kind: Option[Kind]) extends Conflict
      case class ShiftReduce(kind: Option[Kind]) extends Conflict
    }
    
    /** Indicates that a syntax is not LL(1) due to various conflicts.
      *
      * @group conflict
      */
    case class ConflictException(conflicts: Set[Conflict]) extends Exception("Syntax is not LR(1).")

    import Conflict._

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
      sealed trait Symbol

      /**
        * A terminal symbol
        *
        * @param kind the token kind that this terminal accepts
        */
      case class Terminal(kind: Kind) extends Symbol
      /**
        * A non-terminal symbol
        *
        * @param id the id used to identify this non-terminal
        */
      case class NonTerminal(id: Id) extends Symbol

      /**
        * A trait for a grammar production rule
        */
      sealed trait Rule {
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
      case class TransformRule[A, B](ntId: Id, f: B => A, symbol: Symbol) extends Rule
      /**
        * A normal rule without transformation
        *
        * @param ntId    the id of the non-terminal associated with this rule
        * @param symbols the sequence of symbols that the non-terminal expands to
        */
      case class NormalRule0[A](ntId: Id, value: A) extends Rule
      case class NormalRule1(ntId: Id, symbol0: Symbol) extends Rule
      case class NormalRule2(ntId: Id, symbol0: Symbol, symbol1: Symbol) extends Rule
      /**
        * A rule for the `Failure` syntax
        */
      case class FailureRule(ntId: Id) extends Rule

      /**
        * Transform a `Syntax` into a sequence of rules
        *
        * @param syntax the tree to transform
        * @return       the sequence of rules
        *
        * @note inspired form scallion.syntactic.visualization.Grammars
        */
      def getRules[A](syntax: Syntax[A]) = {
        var nextId: Id = 1
        var ids = Map[Syntax[_], Id]()

        def newId[B](next: Syntax[B]): Id = {
          val res = nextId
          nextId += 1
          ids += next -> res
          res
        }

        def createRuleFor[B](s: Syntax[B]): (Symbol, Vector[Rule]) =
          if (ids contains s)
            (NonTerminal(ids(s)), Vector())
          else s match {
            case Elem(kind) =>
              (Terminal(kind), Vector())
            case Disjunction(left, right) =>
              val id = newId(s)
              val (s0, rules0) = createRuleFor(left)
              val (s1, rules1) = createRuleFor(right)
              (NonTerminal(id), Vector(NormalRule1(id, s0), NormalRule1(id, s1)) ++ rules0 ++ rules1)
            case Failure() =>
              val id = newId(s)
              (NonTerminal(id), Vector(FailureRule(id)))
            case Sequence(left, right) =>
              val id = newId(s)
              val (s0, rules0) = createRuleFor(left)
              val (s1, rules1) = createRuleFor(right)
              (NonTerminal(id), NormalRule2(id, s0, s1) +: (rules0 ++ rules1))
            case Success(value, _) =>
              val id = newId(s)
              (NonTerminal(id), Vector(NormalRule0(id, value)))
            case Transform(function, _, inner) =>
              val id = newId(s)
              val (s0, rules0) = createRuleFor(inner)
              (NonTerminal(id), TransformRule(id, function, s0) +: rules0)
            case Recursive(recid, inner) =>
              val id = newId(s)
              val (s0, rules0) = createRuleFor(inner)
              (NonTerminal(id), NormalRule1(id, s0) +: rules0)
          }

        val (s0, rules) = createRuleFor(syntax)
        val rulesById = (NormalRule1(0, s0) +: rules) groupBy (_.ntId)
        (rulesById, getFirstSets(rulesById, nextId))
      }

      def getFirstSets(rulesById: Map[Id, Vector[Rule]], maxId: Id): (Map[Id, Set[Option[Kind]]], Map[Id, Boolean]) = {
        @tailrec
        def buildNullable(current: Map[Id, Boolean]): Map[Id, Boolean] = {
          val res = rulesById.mapValues(_.exists {
            case FailureRule(_) => false
            case NormalRule0(_, _) => true
            case NormalRule1(_, Terminal(_)) => false
            case NormalRule1(_, NonTerminal(id1)) => current(id1)
            case NormalRule2(_, Terminal(_), Terminal(_)) => false
            case NormalRule2(_, Terminal(_), NonTerminal(id1)) => false
            case NormalRule2(_, NonTerminal(id1), Terminal(_)) => false
            case NormalRule2(_, NonTerminal(id1), NonTerminal(id2)) =>
              current(id1) && current(id2)
            case TransformRule(_, f, Terminal(_)) => false
            case TransformRule(_, f, NonTerminal(id1)) => current(id1)
          })
          if (res == current)
            res
          else 
            buildNullable(res)
        }

        val nullable = buildNullable(((0 until maxId) map (_ -> false)).toMap)

        @tailrec
        def buildFirstSets(current: Map[Id, Set[Option[Kind]]]) : Map[Id, Set[Option[Kind]]] = {
          val res = rulesById.mapValues(_.toSet[Rule] flatMap {
            case NormalRule2(_, Terminal(k), _) => Set[Option[Kind]](Some(k))
            case NormalRule2(_, NonTerminal(id), Terminal(k)) => 
              if (nullable(id))
                current(id) + Some(k)
              else 
                current(id)
            case NormalRule2(_, NonTerminal(id1), NonTerminal(id2)) =>
              if (nullable(id1))
                current(id1) ++ current(id2)
              else
                current(id1)
            case NormalRule1(_, Terminal(k)) => Set[Option[Kind]](Some(k))
            case NormalRule1(_, NonTerminal(id)) => current(id)
            case TransformRule(_, _, Terminal(k)) => Set[Option[Kind]](Some(k))
            case TransformRule(_, _, NonTerminal(id)) => current(id)
            case NormalRule0(_, _) => Set[Option[Kind]]()
            case FailureRule(_) => Set[Option[Kind]]()
          })
          if (res == current)
            res
          else
            buildFirstSets(res)
        }

        (buildFirstSets(((0 until maxId) map (_ -> Set[Option[Kind]]())).toMap), nullable)
      }
    }

    import grammar._

    object item {
      type State = Int
      sealed trait Action
      case class Shift(nextState: State) extends Action
      case class Reduce(rule: Rule) extends Action
      case object Done extends Action

      type ItemSet = Set[Item]
      trait Item {
        val id: Id
        val followBy: Set[Option[Kind]]
        val rule: Rule
      }
      case class Item0(id: Id, rule: Rule, followBy: Set[Option[Kind]]) extends Item
      case class Item10(id: Id, rule: Rule, followBy: Set[Option[Kind]], follow: Symbol) extends Item
      case class Item11(id: Id, rule: Rule, followBy: Set[Option[Kind]], parsed: Symbol) extends Item
      case class Item20(id: Id, rule: Rule, followBy: Set[Option[Kind]], follow1: Symbol, follow2: Symbol) extends Item
      case class Item21(id: Id, rule: Rule, followBy: Set[Option[Kind]], parsed: Symbol, follow: Symbol) extends Item
      case class Item22(id: Id, rule: Rule, followBy: Set[Option[Kind]], parsed1: Symbol, parsed2: Symbol) extends Item

      def getFirstItem(r: Rule, followBy: Set[Option[Kind]]): Item = r match {
        case FailureRule(ntId) => Item0(ntId, r, followBy)
        case NormalRule0(ntId, _) => Item0(ntId, r, followBy)
        case NormalRule1(ntId, symbol0) => Item10(ntId, r, followBy, symbol0)
        case NormalRule2(ntId, symbol0, symbol1) => Item20(ntId, r, followBy, symbol0, symbol1)
        case TransformRule(ntId, _, symbol) => Item10(ntId, r, followBy, symbol)
      }

      @tailrec
      def close(itemSet: Set[Item])(implicit rulesById: Map[Id, Vector[Rule]], firstSets: Map[Id, Set[Option[Kind]]], nullable: Map[Id, Boolean]): Set[Item] = {
        def closeItem(item: Item): Set[Item] = item match {
          case Item10(id, _, followBy, NonTerminal(id2)) => 
            (item +: (rulesById(id2) map (getFirstItem(_, followBy)))).toSet
          case Item20(id, _, followBy, NonTerminal(id1), Terminal(k)) => 
            (item +: (rulesById(id1) map (getFirstItem(_, Set(Some(k)))))).toSet
          case Item20(id, _, followBy, NonTerminal(id1), NonTerminal(id2)) => 
            val newFollowSet = if (nullable(id2)) firstSets(id2) ++ followBy else firstSets(id2)
            (item +: (rulesById(id1) map (getFirstItem(_, newFollowSet)))).toSet
          case Item21(id, _, followBy, _, NonTerminal(id2)) => 
            (item +: (rulesById(id2) map (getFirstItem(_, followBy)))).toSet
          case _ => Set(item)
        }
        val res = itemSet flatMap closeItem
        if (res == itemSet)
          res
        else
          close(res)
      }

      def generateTables(implicit rulesById: Map[Id, Vector[Rule]], firstSets: Map[Id, Set[Option[Kind]]], nullable: Map[Id, Boolean])
        : (Set[Conflict], State => Map[Option[Kind], Action], State => Id => State) = {
          var conflicts: Set[Conflict] = Set()
          var nextState = 0
          var itemSetToState: Map[ItemSet, State] = Map()
          val queue: Queue[ItemSet] = Queue()
          getStateFor(Set(getFirstItem(rulesById(0)(0), Set(None))))

          def getStateFor(set: ItemSet): State = {
            val closed = close(set)
            itemSetToState.getOrElse(closed, {
              val newState = nextState
              nextState += 1
              itemSetToState += closed -> newState
              queue.enqueue(closed)
              newState
            })
          }

          def genTableForSet(itemSet: ItemSet)(implicit rulesById: Map[Id, Vector[Rule]], firstSets: Map[Id, Set[Option[Kind]]], nullable: Map[Id, Boolean])
          : (Map[Option[Kind], Action], Map[Id, State]) = {
            val grouped = itemSet.groupBy {
              case Item0(_, _, _) => None
              case Item10(_, _, _, follow) => Some(follow)
              case Item11(_, _, _, _) => None
              case Item20(_, _, _, follow1, _) => Some(follow1)
              case Item21(_, _, _, _, follow) => Some(follow)
              case Item22(_, _, _, _, _) => None
            }
            val shifts: Map[Option[Kind], Action] = grouped.collect { 
              case (Some(Terminal(kind)), set) => 
                Some(kind) -> Shift(getStateFor(set map {
                  case Item10(id, rule, followBy, parsed) => 
                    Item11(id, rule, followBy, parsed)
                  case Item20(id, rule, followBy, parsed, follow) => 
                    Item21(id, rule, followBy, parsed, follow)
                  case Item21(id, rule, followBy, parsed1, parsed2) => 
                    Item22(id, rule, followBy, parsed1, parsed2)
                }))
            }
            val goto = grouped.collect {
              case (Some(NonTerminal(id)), set) =>
                id -> getStateFor(set map {
                  case Item10(id, rule, followBy, parsed) => 
                    Item11(id, rule, followBy, parsed)
                  case Item20(id, rule, followBy, parsed, follow) => 
                    Item21(id, rule, followBy, parsed, follow)
                  case Item21(id, rule, followBy, parsed1, parsed2) => 
                    Item22(id, rule, followBy, parsed1, parsed2)
                })
            }
            val reduces: Map[Option[Kind], Action] = grouped.getOrElse(None, Set()).flatMap { item => item.followBy map (_ -> Reduce(item.rule)) }.groupBy(_._1).map {
              case (kind, reducesSet) => 
                if (reducesSet.size > 1) {
                  conflicts += ReduceReduce(kind) 
                }
                if (reducesSet.head._2.rule == rulesById(0)(0)) kind -> Done
                else reducesSet.head
            }
            val intersect = reduces.keySet intersect shifts.keySet
            if (!intersect.isEmpty) {
              conflicts ++= intersect map (kind => ShiftReduce(kind))
            }
            (shifts ++ reduces, goto)
          }

          var actionTable: Map[State, Map[Option[Kind], Action]] = Map()
          var gotoTable: Map[State, Map[Id, State]] = Map()
          while (!queue.isEmpty) {
            val itemSet = queue.dequeue()
            val state = itemSetToState(itemSet)
            val (newActions, newGoto) = genTableForSet(itemSet)
            actionTable += state -> newActions
            gotoTable += state -> newGoto
          }
          (conflicts, actionTable, gotoTable)
      }
    }

    import item._

    type State = Int

    object stack {
      sealed trait Stack {
        val state: State
      }

      case object EmptyStack extends Stack {
        val state = 0
      }

      case class ConsStack[A](
        head: StackElem[A],
        tail: Stack
      ) extends Stack {
        val state = head.state
      }

      case class StackElem[A](state: State, value: A, symbol: Symbol)
    }

    import stack._
     
    /** Builds a LL(1) parser from a syntax description.
      * In case the syntax is not LL(1),
      * returns the set of conflicts instead of a parser.
      *
      * @param syntax The description of the syntax.
      * @group parsing
      */
    def build[A](syntax: Syntax[A]): Either[Set[Conflict], Parser[A]] =
      util.Try(apply(syntax, enforceLR1=true)) match {
        case util.Success(parser) => Right(parser)
        case util.Failure(ConflictException(conflicts)) => Left(conflicts)
        case util.Failure(exception) => throw exception
      }

      /** Builds a LR(1) parser from a syntax description.
      *
      * @param syntax     The description of the syntax.
      * @param enforceLL1 Indicates if the method should throw a
      *                   `ConflictException` when the `syntax` is not LR(1).
      *                   `true` by default.
      * @throws ConflictException when the `syntax` is not LR(1) and `enforceLR1` is not set to `false`.
      * @group parsing
      */
    def apply[A](syntax: Syntax[A], enforceLR1: Boolean = true): LR1Parser[A] = {
      implicit val (rulesById, (firstSets, nullable)) = getRules(syntax)
      val (conflicts, actionTable, gotoTable) = generateTables
      if (enforceLR1 && !conflicts.isEmpty) 
        throw ConflictException(conflicts)
      else 
        LR1Parser(EmptyStack)(actionTable, gotoTable)
    }

    /** Result of parsing.
      *
      * @group result
      */
    sealed trait ParseResult[A] {

      /** Parser for the rest of input. */
      val rest: Parser[A]

      /** Returns the parsed value, if any. */
      def getValue: Option[A] = this match {
        case Parsed(value, _) => Some(value)
        case _ => None
      }

      /** Apply the given function on the result of the parse */
      def map[B](f: A => B): ParseResult[B] = this match {
        case Parsed(value, rest)                    => Parsed(f(value), rest.map(f))
        case UnexpectedEnd(expected, rest)          => UnexpectedEnd(expected, rest.map(f))
        case UnexpectedToken(token, expected, rest) => UnexpectedToken(token, expected, rest.map(f))
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
      * @param token    The token at fault.
      * @param expected The set of token that would have been accepted
      * @param rest     Parser at the point of error.
      *
      * @group result
      */
    case class UnexpectedToken[A](token: Token, expected: Set[Kind], rest: Parser[A]) extends ParseResult[A]

    /** Indicates that end of input was unexpectedly encountered.
      *
      * The `syntax` for subsequent input is provided.
      *
      * @param expected The set of token that would have been accepted
      * @param syntax   Syntax at the end of input.
      *
      * @group result
      */
    case class UnexpectedEnd[A](expected: Set[Kind], rest: Parser[A]) extends ParseResult[A]

    /** A parser.
    *
    * @group parsing
    */
    sealed trait Parser[A] { self =>
      /** Parses a sequence of tokens.
        *
        * @group parsing
        */
      def apply(tokens: Iterator[Token]): ParseResult[A]

      /** Apply the given function on the result of the parser.
       *
       * @group parsing
       */
      def map[B](f: A => B): Parser[B] = {
        new Parser[B] {
          def apply(tokens: Iterator[Token]): ParseResult[B] = {
            self.apply(tokens).map(f)
          }
        }
      }
    }
    // token = None means EOF

    case class LR1Parser[A](startingStack: Stack = EmptyStack)(implicit actionTable: State => Map[Option[Kind], Action], gotoTable: State => Id => State) extends Parser[A] {

      private def getAction(state: State, token: Option[Token]): Option[Action] = actionTable(state).get(token map getKind)

      private def getExpected(stack: Stack) = actionTable(stack.state).keySet.collect { case Some(token) => token }

      @tailrec
      private def applyAction(stack: Stack, opt: Option[Token]): Either[ParseResult[A], Stack] = (getAction(stack.state, opt), opt) match {
        case (None, Some(t)) =>
          Left(
            UnexpectedToken(t, getExpected(stack), LR1Parser(stack))
          )
        case (None, None) =>
          Left(
            UnexpectedEnd(getExpected(stack), LR1Parser(stack))
          )
        case (Some(Done), None) => stack match {
          case s: ConsStack[A] =>
            val ConsStack(StackElem(_, v, _), EmptyStack) = s
            Left(Parsed(v, LR1Parser(EmptyStack)))
          case EmptyStack => 
            throw new RuntimeException("No value left !")
        }
        case (Some(Shift(nextState)), Some(t)) =>
          Right(
            ConsStack(StackElem(nextState, t, Terminal(getKind(t))), stack)
          )
        case (Some(Reduce(NormalRule0(ntId, value))), _) =>
          val newState = gotoTable(stack.state)(ntId)
          applyAction(
            ConsStack(StackElem(newState, value, NonTerminal(ntId)), stack), opt
          )
        case (Some(Reduce(NormalRule1(ntId, _))), _) =>
          val ConsStack(StackElem(_, v, _), rest) = stack
          val newState = gotoTable(rest.state)(ntId)
          applyAction(
            ConsStack(StackElem(newState, v, NonTerminal(ntId)), rest), opt
          )
        case (Some(Reduce(NormalRule2(ntId, _, _))), _) =>
          val ConsStack(StackElem(_, v0, _), ConsStack(StackElem(_, v1, _), rest)) = stack
          val newState = gotoTable(rest.state)(ntId)
          val combinedElems = v1 ~ v0
          applyAction(
            ConsStack(StackElem(newState, combinedElems, NonTerminal(ntId)), rest), opt
          )
        case (Some(Reduce(tr: TransformRule[tA, tB])), _) =>
          val ConsStack(StackElem(_, v:tB, _), rest) = stack
          val newState = gotoTable(rest.state)(tr.ntId)
          val transformedValue: tA = tr.f(v)
          applyAction(
            ConsStack(StackElem(newState, transformedValue, NonTerminal(tr.ntId)), rest), opt
          )
        case (Some(Reduce(FailureRule(ntid))), Some(t)) =>
          Left(
            UnexpectedToken(t, Set(), LR1Parser(stack))
          )
        case (_, _) =>
          throw new RuntimeException("ActionTable not correct !")
      }

      override def apply(tokens: Iterator[Token]): ParseResult[A] = {
        val result0 = tokens.foldLeft[Either[ParseResult[A], Stack]](Right(startingStack)) {
          case (eitherStack, t) => eitherStack.flatMap(stack => applyAction(stack, Some(t)))
        }
        val Left(res) = result0.flatMap(stack => applyAction(stack, None))
        res
      }
    }
  }
}

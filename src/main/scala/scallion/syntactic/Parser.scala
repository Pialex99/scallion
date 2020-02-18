package scallion.syntactic

import util.{Try, Success, Failure}

trait Parsing { self: Syntaxes =>
  trait ParserFactory {
    /**
      * Builds a parser form a syntax description.
      *
      * @param syntax   the description of the syntax.
      * @param enforce  indicates if the method should throw a
      *                 `ConflictException` when the `syntax` has a conflict.
      *                 `true` by default.
      * 
      * @throws ConflictException when the `syntax` has a conflict and `enforce` is not set to `false`.
      */
    def apply[A](syntax: Syntax[A], enforce: Boolean = true): Parser[A]

    /** Builds a LL(1) parser from a syntax description.
      * In case the syntax is not LL(1),
      * returns the set of conflicts instead of a parser.
      *
      * @param syntax The description of the syntax.
      * @group parsing
      */
    def build[A](syntax: Syntax[A]): Either[Set[Conflict], Parser[A]] =
      Try(apply(syntax, enforce=true)) match {
        case Success(parser) => Right(parser)
        case Failure(ConflictException(conflicts)) => Left(conflicts)
        case Failure(exception) => throw exception
      }
  }
  /** A parser.
    *
    * @group parsing
    */
  trait Parser[A] { self =>
    /** Syntax corresponding to this parser.
      *
      * @group property
      */
    def syntax: Syntax[A]

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
        def syntax = self.syntax.map(f)

        def apply(tokens: Iterator[Token]): ParseResult[B] = {
          self.apply(tokens).map(f)
        }
      }
    }
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
    * @param token The token at fault.
    * @param rest  Parser at the point of error.
    *
    * @group result
    */
  case class UnexpectedToken[A](token: Token, expected: Set[Kind], rest: Parser[A]) extends ParseResult[A]

  /** Indicates that end of input was unexpectedly encountered.
    *
    * The `syntax` for subsequent input is provided.
    *
    * @param syntax Syntax at the end of input.
    *
    * @group result
    */
  case class UnexpectedEnd[A](expected: Set[Kind], rest: Parser[A]) extends ParseResult[A]

  /** Describes a Parser conflict.
    *
    * @group conflict
    */
  trait Conflict {

    /** Source of the conflict. */
    val source: Syntax.Disjunction[_]
  }

  /** Indicates that a syntax is not LL(1) due to various conflicts.
    *
    * @group conflict
    */
  case class ConflictException(conflicts: Set[Conflict]) extends Exception("Syntax has confilict(s).")
}
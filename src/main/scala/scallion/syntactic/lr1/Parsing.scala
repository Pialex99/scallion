package scallion.syntactic
package lr1

import scallion.util.internal._
import scallion.syntactic._

/** This trait implements LR(1) parsing. */
trait LR1Parsing extends Parsing { self: Syntaxes =>
  /** Factory of LR(1) parsers. */
  object LR1 extends ParserFactory {

    /** Contains the description of the various LR(1) conflicts.
      *
      * @group conflict
      */
    object LR1Conflict {
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
    override def apply[A](syntax: Syntax[A], enforceLR1: Boolean = true): Parser[A] = ???
    
    sealed trait LR1Parser[A] extends Parser[A] { self =>
      
    }
  }
}

package scallion

import org.scalatest._

import scallion.syntactic._

class CYKParserTests extends FlatSpec with Inside with Syntaxes with Operators with cyk.Parsing {

  type Kind = Boolean
  type Token = Boolean

  override def getKind(token: Token): Kind = token

  import CYK._
  "Infinit sytax" should "be parsed" in {
    lazy val s: Syntax[Int] = epsilon(0) | recursive(s).map(_ + 1)
    val parser = CYK(s)
    inside(parser.apply(List().toIterator)) {
      case Parsed(values, _) => 
        assert(!values.hasDefiniteSize)
        assert(values.take(10) == Stream.from(0).take(10))
    }
  }
}
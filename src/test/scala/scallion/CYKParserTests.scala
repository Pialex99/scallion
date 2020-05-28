package scallion

import org.scalatest._

import scallion.syntactic._

class CYKParserTests extends FlatSpec with Inside with Syntaxes with Operators with cyk.Parsing {

  type Kind = Boolean
  type Token = Int

  override def getKind(token: Token): Kind = token >= 0

  import CYK._
  "Elem" should "parse correctly when kind match" in {
    val parser = CYK(elem(true))
    inside(parser.apply(List(1).toIterator)) {
      case Parsed(value, _) => 
        assert(value == 1)
    }
  }

  it should "not parse correctly when kind mismatch" in {
    val parser = CYK(elem(true))
    inside(parser.apply(List(-1).toIterator)) {
      case UnexpectedToken(token, rest) => 
        assert(token == -1)
        inside(rest.apply(List(1).toIterator)) {
          case Parsed(value, _) => 
            assert(value == 1)
        }
    }
  }

  it should "fails for too long input" in {
    val parser = CYK(elem(true))
    inside(parser.apply(List(1, 2).toIterator)) {
      case UnexpectedEnd(rest) => 
    }
  }

  "Infinit sytax" should "be parsed with a single elem" in {
    lazy val s: Syntax[Int] = epsilon(0) | recursive(s).map(_ + 1)
    val parser = CYK(s)
    inside(parser.apply(List().toIterator)) {
      case Parsed(values, _) => 
        assert(values == 0)
    }
  }
}
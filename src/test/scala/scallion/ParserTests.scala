/* Copyright 2019 EPFL, Lausanne
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package scallion

import org.scalatest._

import scallion.syntactic._

object Tokens {
  sealed trait Token
  case class Num(value: Int) extends Token
  case class Bool(value: Boolean) extends Token
  case class Op(value: Char) extends Token
  case class Del(value: Char) extends Token
  case class Kw(value: String) extends Token

  sealed trait TokenClass
  case object NumClass extends TokenClass
  case object BoolClass extends TokenClass
  case class OperatorClass(value: Char) extends TokenClass
  case class DelimiterClass(value: Char) extends TokenClass
  case class KeywordClass(value: String) extends TokenClass
}
import Tokens._

abstract class ParserTests extends FlatSpec with Inside with Syntaxes with Operators with Parsing {

  def builder[A](syntax: Syntax[A]): Parser[A]

  type Token = Tokens.Token
  type Kind = Tokens.TokenClass

  import SafeImplicits._

  override def getKind(token: Token): TokenClass = token match {
    case Num(_) => NumClass
    case Bool(_) => BoolClass
    case Op(value) => OperatorClass(value)
    case Del(value) => DelimiterClass(value)
    case Kw(value) => KeywordClass(value)
  }

  import Syntax._

  // elem

  "elem" should "parse tokens from the specified class" in {
    val parser = builder(elem(NumClass))

    inside(parser(Seq(Num(1)).iterator)) {
      case Parsed(res, rest) => {
        assert(res == Num(1))
      }
    }
  }

  it should "not parse tokens from different classes" in {
    val parser = builder(elem(NumClass))

    inside(parser(Seq(Bool(true)).iterator)) {
      case UnexpectedToken(token, expected, rest) => {
        assert(token == Bool(true))
        assert(expected == Set(NumClass))
      }
    }
  }

  it should "correctly fail at the end of input" in {
    val parser = builder(elem(NumClass))

    inside(parser(Seq().iterator)) {
      case UnexpectedEnd(expected, rest) => {
        assert(expected == Set(NumClass))
      }
    }
  }

  // accept

  "accept" should "parser tokens from the specified class" in {
    val parser = builder(accept(NumClass) {
      case Num(value) => value * 2
    })

    inside(parser(Seq(Num(1)).iterator)) {
      case Parsed(res, rest) => {
        assert(res == 2)
      }
    }
  }

  it should "not parse tokens from different classes" in {
    val parser = builder(accept(NumClass) {
      case Num(value) => value * 2
    })

    inside(parser(Seq(Bool(true)).iterator)) {
      case UnexpectedToken(token, expected, rest) => {
        assert(token == Bool(true))
        assert(expected == Set(NumClass))
      }
    }
  }

  it should "correctly fail at the end of input" in {
    val parser = builder(accept(NumClass) {
      case Num(value) => value * 2
    })

    inside(parser(Seq().iterator)) {
      case UnexpectedEnd(expected, rest) => {
        assert(expected == Set(NumClass))
      }
    }
  }

  // epsilon

  "epsilon" should "correctly return value at the end of input" in {
    val parser = builder(epsilon("ok"))

    inside(parser(Seq().iterator)) {
      case Parsed(res, rest) => {
        assert(res == "ok")
      }
    }
  }

  it should "fail in case of remaining input" in {
    val parser = builder(epsilon("ok"))

    inside(parser(Seq(Bool(true)).iterator)) {
      case UnexpectedToken(token, expected, rest) => {
        assert(token == Bool(true))
        assert(expected == Set())
      }
    }
  }

  // failure

  "failure" should "correctly fail in case of remaining input" in {
    val parser = builder(failure[Any])

    inside(parser(Seq(Bool(true)).iterator)) {
      case UnexpectedToken(token, expected, rest) => {
        assert(token == Bool(true))
        assert(expected == Set())
      }
    }
  }

  // sequencing

  "sequencing" should "parse using the two parsers in sequence" in {
    val parser = builder(elem(BoolClass) ~ elem(NumClass))

    inside(parser(Seq(Bool(true), Num(32)).iterator)) {
      case Parsed(first ~ second, rest) => {
        assert(first == Bool(true))
        assert(second == Num(32))
      }
    }
  }

  it should "use the fact that left might be nullable for parsing" in {
    val parser = builder((elem(BoolClass) | epsilon(Bool(true))) ~ elem(NumClass))

    inside(parser(Seq(Num(32)).iterator)) {
      case Parsed(first ~ second, rest) => {
        assert(first == Bool(true))
        assert(second == Num(32))
      }
    }
  }

  it should "fail at the correct point" in {
    val parser = builder(elem(BoolClass) ~ elem(NumClass))

    inside(parser(Seq(Num(1), Num(2)).iterator)) {
      case UnexpectedToken(token, expected, rest) => {
        assert(token == Num(1))
        assert(expected == Set(BoolClass))
      }
    }

    inside(parser(Seq(Bool(true), Bool(false)).iterator)) {
      case UnexpectedToken(token, expected, rest) => {
        assert(token == Bool(false))
        assert(expected == Set(NumClass))
      }
    }
  }

  // concatenation

  "concatenation" should "parse using the two parsers in sequence" in {
    def f(k: TokenClass): Syntax[Seq[Token]] = elem(k).map(Seq(_))
    val parser = builder(f(BoolClass) ++ f(NumClass))

    inside(parser(Seq(Bool(true), Num(32)).iterator)) {
      case Parsed(res, rest) => {
        assert(res == Seq(Bool(true), Num(32)))
      }
    }
  }

  it should "use the fact that left might be nullable for parsing" in {
    val parser = builder((elem(BoolClass) |
      epsilon(Bool(true))).map(Seq(_)) ++
      elem(NumClass).map(Seq(_)))

    inside(parser(Seq(Num(32)).iterator)) {
      case Parsed(res, rest) => {
        assert(res == Seq(Bool(true), Num(32)))
      }
    }
  }

  it should "fail at the correct point" in {
    val parser = builder(elem(BoolClass).map(Seq(_)) ++ elem(NumClass).map(Seq(_)))

    inside(parser(Seq(Num(1), Num(2)).iterator)) {
      case UnexpectedToken(token, expected, rest) => {
        assert(token == Num(1))
        assert(expected == Set(BoolClass))
      }
    }

    inside(parser(Seq(Bool(true), Bool(false)).iterator)) {
      case UnexpectedToken(token, expected, rest) => {
        assert(token == Bool(false))
        assert(expected == Set(NumClass))
      }
    }
  }

  // disjunction

  "disjunction" should "accept from the first parser" in {
    val parser = builder(elem(BoolClass) | elem(NumClass))

    inside(parser(Seq(Bool(true)).iterator)) {
      case Parsed(res, rest) => {
        assert(res == Bool(true))
      }
    }
  }

  it should "accept from the second parser" in {
    val parser = builder(elem(BoolClass) | elem(NumClass))

    inside(parser(Seq(Num(1)).iterator)) {
      case Parsed(res, rest) => {
        assert(res == Num(1))
      }
    }
  }

  // tagged disjunction

  "tagged disjunction" should "correctly tag values" in {
    val parser = builder(elem(BoolClass) || elem(NumClass))

    inside(parser(Seq(Num(1)).iterator)) {
      case Parsed(res, rest) => {
        assert(res == Right(Num(1)))
      }
    }

    inside(parser(Seq(Bool(true)).iterator)) {
      case Parsed(res, rest) => {
        assert(res == Left(Bool(true)))
      }
    }
  }

  it should "accept different branch types" in {
    val parser = builder(elem(BoolClass).map(_ => "X") || elem(NumClass).map(_ => 42))

    inside(parser(Seq(Num(1)).iterator)) {
      case Parsed(res, rest) => {
        assert(res == Right(42))
      }
    }

    inside(parser(Seq(Bool(true)).iterator)) {
      case Parsed(res, rest) => {
        assert(res == Left("X"))
      }
    }
  }

  // many

  "many" should "parse zero repetitions" in {
    val parser = builder(many(elem(NumClass)))

    inside(parser(Seq().iterator)) {
      case Parsed(res, rest) => {
        assert(res == Seq())
      }
    }
  }

  it should "parse one repetition" in {
    val parser = builder(many(elem(NumClass)))

    inside(parser(Seq(Num(12)).iterator)) {
      case Parsed(res, rest) => {
        assert(res == Seq(Num(12)))
      }
    }
  }

  it should "parse several repetitions" in {
    val parser = builder(many(elem(NumClass)))

    inside(parser(Seq(Num(12), Num(34), Num(1)).iterator)) {
      case Parsed(res, rest) => {
        assert(res == Seq(Num(12), Num(34), Num(1)))
      }
    }
  }

  it should "not fix choices" in {
    val parser = builder(many(elem(NumClass) | elem(BoolClass)))

    inside(parser(Seq(Num(12), Bool(true), Num(1), Num(12), Bool(false)).iterator)) {
      case Parsed(res, rest) => {
        assert(res == Seq(Num(12), Bool(true), Num(1), Num(12), Bool(false)))
      }
    }
  }

  it should "fail when inner parser fails" in {
    val parser = builder(many(elem(NumClass)))

    inside(parser(Seq(Num(12), Bool(true), Num(1)).iterator)) {
      case UnexpectedToken(token, expected, rest) => {
        assert(token == Bool(true))
        assert(expected == Set(NumClass))
      }
    }
  }

  // many1

  "many1" should "not parse zero repetitions" in {
    val parser = builder(many1(elem(NumClass)))

    inside(parser(Seq().iterator)) {
      case UnexpectedEnd(expected, rest) => {
        assert(expected == Set(NumClass))
      }
    }
  }

  it should "parse one repetition" in {
    val parser = builder(many1(elem(NumClass)))

    inside(parser(Seq(Num(12)).iterator)) {
      case Parsed(res, rest) => {
        assert(res == Seq(Num(12)))
      }
    }
  }

  it should "parse several repetitions" in {
    val parser = builder(many1(elem(NumClass)))

    inside(parser(Seq(Num(12), Num(34), Num(1)).iterator)) {
      case Parsed(res, rest) => {
        assert(res == Seq(Num(12), Num(34), Num(1)))
      }
    }
  }

  it should "not fix choices" in {
    val parser = builder(many1(elem(NumClass) | elem(BoolClass)))

    inside(parser(Seq(Num(12), Bool(true), Num(1), Num(12), Bool(false)).iterator)) {
      case Parsed(res, rest) => {
        assert(res == Seq(Num(12), Bool(true), Num(1), Num(12), Bool(false)))
      }
    }
  }

  it should "fail when inner parser fails" in {
    val parser = builder(many1(elem(NumClass)))

    inside(parser(Seq(Num(12), Bool(true), Num(1)).iterator)) {
      case UnexpectedToken(token, expected, rest) => {
        assert(token == Bool(true))
        assert(expected == Set(NumClass))
      }
    }
  }

  // recursive

  "recursive" should "allow building recursive parsers" in {
    lazy val syntax: Syntax[Seq[Token]] = recursive {
      elem(BoolClass) +: syntax | epsilon(Seq())
    }

    val parser = builder(syntax)

    inside(parser(Seq(Bool(true), Bool(false)).iterator)) {
      case Parsed(res, rest) => {
        assert(res == Seq(Bool(true), Bool(false)))
      }
    }
  }
}

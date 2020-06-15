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

import Tokens._
import scallion.BracketsTockens.Tocken

class LR1ParserTests extends FlatSpec with Inside with Syntaxes with Operators with lr1.Parsing {

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
  import LR1._

  // elem

  "elem" should "parse tokens from the specified class" in {
    val parser = LR1(elem(NumClass))

    inside(parser(Seq(Num(1)).iterator)) {
      case Parsed(res, rest) => {
        assert(res == Num(1))
      }
    }
  }

  it should "not parse tokens from different classes" in {
    val parser = LR1(elem(NumClass))

    inside(parser(Seq(Bool(true)).iterator)) {
      case UnexpectedToken(token, expected, rest) => {
        assert(token == Bool(true))
        assert(expected == Set(NumClass))
      }
    }
  }

  it should "correctly fail at the end of input" in {
    val parser = LR1(elem(NumClass))

    inside(parser(Seq().iterator)) {
      case UnexpectedEnd(expected, rest) => {
        assert(expected == Set(NumClass))
      }
    }
  }

  // accept

  "accept" should "parser tokens from the specified class" in {
    val parser = LR1(accept(NumClass) {
      case Num(value) => value * 2
    })

    inside(parser(Seq(Num(1)).iterator)) {
      case Parsed(res, rest) => {
        assert(res == 2)
      }
    }
  }

  it should "not parse tokens from different classes" in {
    val parser = LR1(accept(NumClass) {
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
    val parser = LR1(accept(NumClass) {
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
    val parser = LR1(epsilon("ok"))

    inside(parser(Seq().iterator)) {
      case Parsed(res, rest) => {
        assert(res == "ok")
      }
    }
  }

  it should "fail in case of remaining input" in {
    val parser = LR1(epsilon("ok"))

    inside(parser(Seq(Bool(true)).iterator)) {
      case UnexpectedToken(token, expected, rest) => {
        assert(token == Bool(true))
        assert(expected == Set())
      }
    }
  }

  // failure

  "failure" should "correctly fail in case of end of input" in {
    val parser = LR1(failure[Any])

    inside(parser(Seq().iterator)) {
      case UnexpectedEnd(expected, rest) => {
        assert(expected.isEmpty)
      }
    }
  }

  it should "correctly fail in case of remaining input" in {
    val parser = LR1(failure[Any])

    inside(parser(Seq(Bool(true)).iterator)) {
      case UnexpectedToken(token, expected, rest) => {
        assert(token == Bool(true))
        assert(expected.isEmpty)
      }
    }
  }

  // sequencing

  "sequencing" should "parse using the two parsers in sequence" in {
    val parser = LR1(elem(BoolClass) ~ elem(NumClass))

    inside(parser(Seq(Bool(true), Num(32)).iterator)) {
      case Parsed(first ~ second, rest) => {
        assert(first == Bool(true))
        assert(second == Num(32))
      }
    }
  }

  it should "use the fact that left might be nullable for parsing" in {
    val parser = LR1((elem(BoolClass) | epsilon(Bool(true))) ~ elem(NumClass))

    inside(parser(Seq(Num(32)).iterator)) {
      case Parsed(first ~ second, rest) => {
        assert(first == Bool(true))
        assert(second == Num(32))
      }
    }
  }

  it should "fail at the correct point" in {
    val parser = LR1(elem(BoolClass) ~ elem(NumClass))

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
    val parser = LR1(f(BoolClass) ++ f(NumClass))

    inside(parser(Seq(Bool(true), Num(32)).iterator)) {
      case Parsed(res, rest) => {
        assert(res == Seq(Bool(true), Num(32)))
      }
    }
  }

  it should "use the fact that left might be nullable for parsing" in {
    val parser = LR1((elem(BoolClass) |
      epsilon(Bool(true))).map(Seq(_)) ++
      elem(NumClass).map(Seq(_)))

    inside(parser(Seq(Num(32)).iterator)) {
      case Parsed(res, rest) => {
        assert(res == Seq(Bool(true), Num(32)))
      }
    }
  }

  it should "fail at the correct point" in {
    val parser = LR1(elem(BoolClass).map(Seq(_)) ++ elem(NumClass).map(Seq(_)))

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
    val parser = LR1(elem(BoolClass) | elem(NumClass))

    inside(parser(Seq(Bool(true)).iterator)) {
      case Parsed(res, rest) => {
        assert(res == Bool(true))
      }
    }
  }

  it should "accept from the second parser" in {
    val parser = LR1(elem(BoolClass) | elem(NumClass))

    inside(parser(Seq(Num(1)).iterator)) {
      case Parsed(res, rest) => {
        assert(res == Num(1))
      }
    }
  }

  // tagged disjunction

  "tagged disjunction" should "correctly tag values" in {
    val parser = LR1(elem(BoolClass) || elem(NumClass))

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
    val parser = LR1(elem(BoolClass).map(_ => "X") || elem(NumClass).map(_ => 42))

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
    val parser = LR1(many(elem(NumClass)))

    inside(parser(Seq().iterator)) {
      case Parsed(res, rest) => {
        assert(res == Seq())
      }
    }
  }

  it should "parse one repetition" in {
    val parser = LR1(many(elem(NumClass)))

    inside(parser(Seq(Num(12)).iterator)) {
      case Parsed(res, rest) => {
        assert(res == Seq(Num(12)))
      }
    }
  }

  it should "parse several repetitions" in {
    val parser = LR1(many(elem(NumClass)))

    inside(parser(Seq(Num(12), Num(34), Num(1)).iterator)) {
      case Parsed(res, rest) => {
        assert(res == Seq(Num(12), Num(34), Num(1)))
      }
    }
  }

  it should "not fix choices" in {
    val parser = LR1(many(elem(NumClass) | elem(BoolClass)))

    inside(parser(Seq(Num(12), Bool(true), Num(1), Num(12), Bool(false)).iterator)) {
      case Parsed(res, rest) => {
        assert(res == Seq(Num(12), Bool(true), Num(1), Num(12), Bool(false)))
      }
    }
  }

  it should "fail when inner parser fails" in {
    val parser = LR1(many(elem(NumClass)))

    inside(parser(Seq(Num(12), Bool(true), Num(1)).iterator)) {
      case UnexpectedToken(token, expected, rest) => {
        assert(token == Bool(true))
        assert(expected == Set(NumClass))
      }
    }
  }

  // many1

  "many1" should "not parse zero repetitions" in {
    val parser = LR1(many1(elem(NumClass)))

    inside(parser(Seq().iterator)) {
      case UnexpectedEnd(expected, rest) => {
        assert(expected == Set(NumClass))
      }
    }
  }

  it should "parse one repetition" in {
    val parser = LR1(many1(elem(NumClass)))

    inside(parser(Seq(Num(12)).iterator)) {
      case Parsed(res, rest) => {
        assert(res == Seq(Num(12)))
      }
    }
  }

  it should "parse several repetitions" in {
    val parser = LR1(many1(elem(NumClass)))

    inside(parser(Seq(Num(12), Num(34), Num(1)).iterator)) {
      case Parsed(res, rest) => {
        assert(res == Seq(Num(12), Num(34), Num(1)))
      }
    }
  }

  it should "not fix choices" in {
    val parser = LR1(many1(elem(NumClass) | elem(BoolClass)))

    inside(parser(Seq(Num(12), Bool(true), Num(1), Num(12), Bool(false)).iterator)) {
      case Parsed(res, rest) => {
        assert(res == Seq(Num(12), Bool(true), Num(1), Num(12), Bool(false)))
      }
    }
  }

  it should "fail when inner parser fails" in {
    val parser = LR1(many1(elem(NumClass)))

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

    val parser = LR1(syntax)

    inside(parser(Seq(Bool(true), Bool(false)).iterator)) {
      case Parsed(res, rest) => {
        assert(res == Seq(Bool(true), Bool(false)))
      }
    }
  }

  it should "allow building left recursive parsers" in {
    lazy val syntax: Syntax[Seq[Token]] = recursive {
      syntax :+ elem(BoolClass) | epsilon(Seq())
    }

    val parser = LR1(syntax)

    inside(parser(Seq(Bool(true), Bool(false)).iterator)) {
      case Parsed(res, rest) => {
        assert(res == Seq(Bool(true), Bool(false)))
      }
    }
  }

  // LR1 conflicts

  import LR1.Conflict._

  "LR1 conflicts" should "have a SR conflict for the language of palindroms" in {
    lazy val syntax: Syntax[Seq[Token]] = recursive {
      elem(BoolClass) +: syntax :+ elem(BoolClass) |
      elem(NumClass) +: syntax :+ elem(NumClass) |
      epsilon(Seq())
    }

    val res = LR1.build(syntax)
    assert(res.isLeft)

    val Left(conflicts) = res
    assert(conflicts.size > 1)
    inside((conflicts.toSeq(0), conflicts.toSeq(1))) {
      case (ShiftReduce(kind1), ShiftReduce(kind2)) => 
        assert(kind1.isDefined)
        assert(kind2.isDefined)
        assert(kind1.get == BoolClass || kind2.get == BoolClass)
        assert(kind1.get == NumClass || kind2.get == NumClass)
    }
  }

  it should "catch ambiguous language" in {
    lazy val syntax: Syntax[Int] = recursive {
      epsilon(0) | syntax map (_ + 1)
    }

    val res = LR1.build(syntax)
    assert(res.isLeft)

    val Left(conflicts) = res
    assert(conflicts.size == 1)
    inside(conflicts.head) {
      case ReduceReduce(kind) => 
        assert(kind.isEmpty)
    }
  }

  it should "catch ambiguous language 2" in {
    import scala.language.implicitConversions
    implicit def cast(c: Char) = elem(DelimiterClass(c))
    lazy val syntax: Syntax[Unit] = recursive {
      (syntax ~ '(' ~ syntax ~ ')' ~ syntax ).map(_ => ()) | epsilon((): Unit)
    }
    assertThrows[ConflictException] {
      LR1(syntax)
    }
  }
}

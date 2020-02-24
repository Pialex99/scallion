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

object CalculatorTokens {
  sealed trait Token
  case class Num(value: Int) extends Token
  case object Plus extends Token
  case object Times extends Token

  sealed trait TokenClass
  case object NumClass extends TokenClass
  case object PlusClass extends TokenClass
  case object TimesClass extends TokenClass
}

import CalculatorTokens._

class SimpleCalulatorTests extends FlatSpec with Inside with Syntaxes with Operators with lr1.LR1Parsing {

  type Token = CalculatorTokens.Token
  type Kind = CalculatorTokens.TokenClass

  import SafeImplicits._

  override def getKind(token: Token): TokenClass = token match {
    case Num(_) => NumClass
    case Plus => PlusClass
    case Times => TimesClass
  }

  import Syntax._
  import Implicits._
  
  val b: Syntax[Int] = accept(NumClass) { case Num(n) => n }

  val e: Syntax[Int] = oneOf(
    (recursive(e) ~ elem(PlusClass).skip ~ b) map {
      case n1 ~ n2 => n1 + n2
    },
    (recursive(e) ~ elem(TimesClass).skip ~ b) map {
      case n1 ~ n2 => n1 * n2
    },
    b
  )

  val parser = LR1(e)

  "hello" should "say" in {
    assert(true)
  }
}

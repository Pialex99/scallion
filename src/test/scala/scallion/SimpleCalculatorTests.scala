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
  case class Id(id: Int) extends Token
  case class Num(value: Int) extends Token
  case object Plus extends Token
  case object Times extends Token

  sealed trait TokenClass
  object IdClass extends TokenClass
  object NumClass extends TokenClass
  object PlusClass extends TokenClass
  object TimesClass extends TokenClass
}

import CalculatorTokens._

class SimpleCalulatorTests extends FlatSpec with Inside with Syntaxes with Operators with lr1.LR1Parsing {

  type Token = CalculatorTokens.Token
  type Kind = CalculatorTokens.TokenClass

  import SafeImplicits._

  override def getKind(token: Token): TokenClass = token match {
    case Id(_) => IdClass
    case Num(_) => NumClass
    case Plus => PlusClass
    case Times => TimesClass
  }

  import Syntax._
  import Implicits._
  
  val sums: Syntax[Int] = recursive(
    (sums ~ elem(PlusClass) ~ products).map {
      case n1 ~ _ ~ n2 => n1 + n2
    } | products
  )
  val products: Syntax[Int] = recursive(
    (products ~ elem(TimesClass) ~ value).map {
      case n1 ~ _ ~ n2 => n1 * n2 
    } | value
  )
  val idValues = (id: Int) => id + 1
  val value: Syntax[Int] = elem(NumClass).map { case Num(n) => n } |
    elem(IdClass).map { case Id(id) =>  idValues(id) }

  //val parser = LR1(sums)

  import LR1._
  import LR1.grammar._
  import LR1.stack._
  import LR1.item._
  val actionTable: Vector[Map[Option[Kind], Action]] = Vector(
    Map(Some(NumClass) -> Shift(8), Some(IdClass) -> Shift(9)),
    Map(Some(PlusClass) -> Shift(2), None -> Done),
    Map(Some(NumClass) -> Shift(8), Some(IdClass) -> Shift(9)),
    Map(Some(TimesClass) -> Shift(5), Some(PlusClass) -> Reduce(???))
  )
  val gotoTable: Vector[Map[Id, State]] = Vector(

  )
  val handMaidParser = LR1Parser(EmptyStack)(actionTable, gotoTable)

  "hello" should "say" in {
    assert(true)
  }
}

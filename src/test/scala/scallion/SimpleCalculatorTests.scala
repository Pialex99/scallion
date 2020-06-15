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
  case object IdClass extends TokenClass
  case object NumClass extends TokenClass
  case object PlusClass extends TokenClass
  case object TimesClass extends TokenClass
}

import CalculatorTokens._

class SimpleCalulatorTests extends FlatSpec with Inside with Syntaxes with Operators with lr1.Parsing {

  type Token = CalculatorTokens.Token
  type Kind = CalculatorTokens.TokenClass

  override def getKind(token: Token): TokenClass = token match {
    case Id(_) => IdClass
    case Num(_) => NumClass
    case Plus => PlusClass
    case Times => TimesClass
  }

  import LR1._
  import LR1.grammar._
  import LR1.stack._
  import LR1.item._

  
  /*
    rSum1 : 0 -> 1
    rSum2 : 1 -> 2
    rSum3 : 1 -> 6
    rSum4 : 2 -m> 3
    rSum5 : 3 -> 4 6
    rSum6 : 4 -> 5 +
    rSum7 : 5 -> 1
    rSum8 : 6 -m> n
  */
  val rSum1 = NormalRule1(0, NonTerminal(1))
  val rSum2 = NormalRule1(1, NonTerminal(2))
  val rSum3 = NormalRule1(1, NonTerminal(6))
  val rSum4 = TransformRule[Int, Int ~ Token ~ Int](2, { case n1 ~ Plus ~ n2 => n1 + n2 }, NonTerminal(3))
  val rSum5 = NormalRule2(3, NonTerminal(4), NonTerminal(5))
  val rSum6 = NormalRule2(4, NonTerminal(5), Terminal(PlusClass))
  val rSum7 = NormalRule1(5, NonTerminal(1))
  val rSum8 = TransformRule[Int, Num](6, { case Num(n) => n }, Terminal(NumClass))

  val actionSumTable: Vector[Map[Option[Kind], Action]] = Vector(
/* 0 */    Map(Some(NumClass) -> Shift(7)),
/* 1 */    Map(Some(PlusClass) -> Reduce(rSum7), None -> Done),
/* 2 */    Map(Some(PlusClass) -> Reduce(rSum2), None -> Reduce(rSum2)),
/* 3 */    Map(Some(PlusClass) -> Reduce(rSum3), None -> Reduce(rSum3)),
/* 4 */    Map(Some(PlusClass) -> Reduce(rSum4), None -> Reduce(rSum4)),
/* 5 */    Map(Some(NumClass) -> Shift(7)),
/* 6 */    Map(Some(PlusClass) -> Shift(9)),
/* 7 */    Map(Some(PlusClass) -> Reduce(rSum8), None -> Reduce(rSum8)),
/* 8 */    Map(Some(PlusClass) -> Reduce(rSum5), None -> Reduce(rSum5)),
/* 9 */    Map(Some(NumClass) -> Reduce(rSum6))
  )
  val gotoSumTable: Vector[Map[Id, State]] = Vector(
/* 0 */   Map(1 -> 1, 2 -> 2, 6 -> 3, 3 -> 4, 4 -> 5, 5 -> 6),
/* 1 */   Map(),
/* 2 */   Map(),
/* 3 */   Map(),
/* 4 */   Map(),
/* 5 */   Map(6 -> 8),
/* 6 */   Map(),
/* 7 */   Map(),
/* 8 */   Map(),
/* 9 */   Map()
  )
  val handMaidSumParser = LR1Parser[Int](EmptyStack)(actionSumTable, gotoSumTable)

  "HandMaisSumParser" should "1 = 1" in {
    val result = handMaidSumParser(List(Num(1)).iterator)
    assert(result.getValue == Some(1))
  }

  it should "2 + 5 = 7" in {
    val result = handMaidSumParser(List(Num(2), Plus, Num(5)).iterator)
    assert(result.getValue == Some(7))
  }
  
  it should "4 + 3 + 8 = 15" in {
    val result = handMaidSumParser(List(Num(4), Plus, Num(3), Plus, Num(8)).iterator)
    assert(result.getValue == Some(15))
  } 

  it should "fails for +" in {
    val result = handMaidSumParser(List(Plus).iterator)
    assert(result.getValue == None)
    result match {
      case UnexpectedToken(Plus, expected, rest) => 
        assert(expected == Set(NumClass))
        assert(rest(List(Num(1)).iterator).getValue == Some(1))
      case _ => fail()
    }
  }

  it should "fails for 1 +" in {
    val result = handMaidSumParser(List(Num(1), Plus).iterator)
    assert(result.getValue == None)
    result match {
      case UnexpectedEnd(expected, rest) => 
        assert(expected == Set(NumClass))
        assert(rest(List(Num(4)).iterator).getValue == Some(5))
      case _ => fail()
    }
  }

  it should "fails for 3 + +" in {
    val result = handMaidSumParser(List(Num(3), Plus, Plus).iterator)
    assert(result.getValue == None)
    result match {
      case UnexpectedToken(Plus, expected, rest) => 
        assert(expected == Set(NumClass))
        assert(rest(List(Num(4)).iterator).getValue == Some(7))
      case _ => fail()
    }
  }

  it should "fails for 3 4" in {
    val result = handMaidSumParser(List(Num(3), Num(4)).iterator)
    assert(result.getValue == None)
    result match {
      case UnexpectedToken(Num(4), expected, rest) => 
        assert(expected == Set(PlusClass))
        assert(rest(Nil.iterator).getValue == Some(3))
      case _ => fail()
    }
  }

  val idValues = (id: Int) => id + 1
  val value: Syntax[Int] = accept(NumClass) { case Num(n) => n } |
    accept(IdClass) { case Id(id) =>  idValues(id) }

  val products: Syntax[Int] = 
    (recursive(products) ~ elem(TimesClass) ~ value).map {
      case n1 ~ _ ~ n2 => n1 * n2 
    } | value

  val sums: Syntax[Int] = 
    (recursive(sums) ~ elem(PlusClass) ~ products).map {
      case n1 ~ _ ~ n2 => n1 + n2
    } | products
  
  val parser = LR1(sums)

  "LR1 parser" should "1 = 1" in {
    val result = parser(List(Num(1)).iterator)
    assert(result.getValue == Some(1))
  }

  it should "2 + 5 = 7" in {
    val result = parser(List(Num(2), Plus, Num(5)).iterator)
    assert(result.getValue == Some(7))
  }
  
  it should "4 + 3 + 8 = 15" in {
    val result = parser(List(Num(4), Plus, Num(3), Plus, Num(8)).iterator)
    assert(result.getValue == Some(15))
  }
  
  it should "2 * 3 = 6" in {
    val result = parser(List(Num(2), Times, Num(3)).iterator)
    assert(result.getValue == Some(6))
  }

  it should "4 * 3 * 7 = 84" in {
    val result = parser(List(Num(4), Times, Num(3), Times, Num(7)).iterator)
    assert(result.getValue == Some(84))
  }

  it should "3 * 5 + 4 = 19" in {
    val result = parser(List(Num(3), Times, Num(5), Plus, Num(4)).iterator)
    assert(result.getValue == Some(19))
  }

  it should "8 + 4 * 7 = 36" in {
    val result = parser(List(Num(8), Plus, Num(4), Times, Num(7)).iterator)
    assert(result.getValue == Some(36))
  }

  it should "7 + 1 * 6 + 3 = 16" in {
    val result = parser(List(Num(7), Plus, Num(1), Times, Num(6), Plus, Num(3)).iterator)
    assert(result.getValue == Some(16))
  }

   it should "7 * 2 + 4 * 1 * 6 + 3 = 41" in {
    val result = parser(List(Num(7), Times, Num(2), Plus, Num(4), Times, Num(1), Times, Num(6), Plus, Num(3)).iterator)
    assert(result.getValue == Some(41))
  }

  it should "fails for +" in {
    val result = parser(List(Plus).iterator)
    assert(result.getValue == None)
    result match {
      case UnexpectedToken(Plus, expected, rest) => 
        assert(expected == Set(NumClass, IdClass))
        assert(rest(List(Num(1)).iterator).getValue == Some(1))
      case _ => fail()
    }
  }

  it should "fails for 1 +" in {
    val result = parser(List(Num(1), Plus).iterator)
    assert(result.getValue == None)
    result match {
      case UnexpectedEnd(expected, rest) => 
        assert(expected == Set(NumClass, IdClass))
        assert(rest(List(Num(4)).iterator).getValue == Some(5))
      case _ => fail()
    }
  }

  it should "fails for 2 *" in {
    val result = parser(List(Num(2), Times).iterator)
    assert(result.getValue == None)
    result match {
      case UnexpectedEnd(expected, rest) => 
        assert(expected == Set(NumClass, IdClass))
        assert(rest(List(Num(4)).iterator).getValue == Some(8))
      case _ => fail()
    }
  }

  it should "fails for 2 + 5 *" in {
    val result = parser(List(Num(2), Plus, Num(5), Times).iterator)
    assert(result.getValue == None)
    result match {
      case UnexpectedEnd(expected, rest) => 
        assert(expected == Set(NumClass, IdClass))
        assert(rest(List(Num(3)).iterator).getValue == Some(17))
      case _ => fail()
    }
  }

  it should "fails for 3 + +" in {
    val result = parser(List(Num(3), Plus, Plus).iterator)
    assert(result.getValue == None)
    result match {
      case UnexpectedToken(Plus, expected, rest) => 
        assert(expected == Set(NumClass, IdClass))
        assert(rest(List(Num(4)).iterator).getValue == Some(7))
      case _ => fail()
    }
  }

  it should "fails for 3 * +" in {
    val result = parser(List(Num(3), Times, Plus).iterator)
    assert(result.getValue == None)
    result match {
      case UnexpectedToken(Plus, expected, rest) => 
        assert(expected == Set(NumClass, IdClass))
        assert(rest(List(Num(4)).iterator).getValue == Some(12))
      case _ => fail()
    }
  }

  it should "fails for 3 4" in {
    val result = parser(List(Num(3), Num(4)).iterator)
    assert(result.getValue == None)
    result match {
      case UnexpectedToken(Num(4), expected, rest) => 
        assert(expected == Set(PlusClass, TimesClass))
        assert(rest(Nil.iterator).getValue == Some(3))
      case _ => fail()
    }
  }

  /*
    r1  : 0 -> 1
    r2  : 1 -> 2
    r3  : 1 -> 6
    r4  : 2 -m> 3
    r5  : 3 -> 4 6
    r6  : 4 -> 5 +
    r7  : 5 -> 1
    r8  : 6 -> 7
    r9  : 6 -> 11
    r10 : 7 -m> 8
    r11 : 8 -> 9 11
    r12 : 9 -> 10 *
    r13 : 10 -> 6
    r14 : 11 -> 12
    r15 : 11 -> 13
    r16 : 12 -m> n
    r17 : 13 -m> id
  */
  val r1 = NormalRule1(0, NonTerminal(1))
  val r2 = NormalRule1(1, NonTerminal(2))
  val r3 = NormalRule1(1, NonTerminal(6))
  val r4 = TransformRule[Int, Int ~ Token ~ Int](2, { case n1 ~ Plus ~ n2 => n1 + n2 }, NonTerminal(3))
  val r5 = NormalRule2(3, NonTerminal(4), NonTerminal(5))
  val r6 = NormalRule2(4, NonTerminal(5), Terminal(PlusClass))
  val r7 = NormalRule1(5, NonTerminal(1))
  val r8 = NormalRule1(6, NonTerminal(7))
  val r9 = NormalRule1(6, NonTerminal(11))
  val r10 = TransformRule[Int, Int ~ Token ~ Int](7, { case n1 ~ Times ~ n2 => n1 * n2 }, NonTerminal(8))
  val r11 = NormalRule2(8, NonTerminal(9), NonTerminal(11))
  val r12 = NormalRule2(9, NonTerminal(10), Terminal(TimesClass))
  val r13 = NormalRule1(10, NonTerminal(6))
  val r14 = NormalRule1(11, NonTerminal(12))
  val r15 = NormalRule1(11, NonTerminal(13))
  val r16 = TransformRule[Int, Num](12, { case Num(n) => n }, Terminal(NumClass))
  val r17 = TransformRule[Int, CalculatorTokens.Id](13, { case Id(i) => idValues(i) }, Terminal(IdClass))

  val actionTable: Vector[Map[Option[Kind], Action]] = Vector(
/* 0 */    Map(Some(NumClass) -> Shift(14), Some(IdClass) -> Shift(15)),
/* 1 */    Map(Some(PlusClass) -> Reduce(r7), None -> Done),
/* 2 */    Map(Some(PlusClass) -> Reduce(r2), None -> Reduce(r2)),
/* 3 */    Map(Some(PlusClass) -> Reduce(r3), Some(TimesClass) -> Reduce(r13), None -> Reduce(r3)),
/* 4 */    Map(Some(PlusClass) -> Reduce(r4), None -> Reduce(r4)),
/* 5 */    Map(Some(NumClass) -> Shift(14), Some(IdClass) -> Shift(15)),
/* 6 */    Map(Some(PlusClass) -> Shift(17)),
/* 7 */    Map(Some(PlusClass) -> Reduce(r8), Some(TimesClass) -> Reduce(r8), None -> Reduce(r8)),
/* 8 */    Map(Some(PlusClass) -> Reduce(r9), Some(TimesClass) -> Reduce(r9),  None -> Reduce(r9)),
/* 9 */    Map(Some(PlusClass) -> Reduce(r10), Some(TimesClass) -> Reduce(r10),  None -> Reduce(r10)),
/*10 */    Map(Some(NumClass) -> Shift(14), Some(IdClass) -> Shift(15)),
/*11 */    Map(Some(TimesClass) -> Shift(19)),
/*12 */    Map(Some(PlusClass) -> Reduce(r14), Some(TimesClass) -> Reduce(r14),  None -> Reduce(r14)),
/*13 */    Map(Some(PlusClass) -> Reduce(r15), Some(TimesClass) -> Reduce(r15),  None -> Reduce(r15)),
/*14 */    Map(Some(PlusClass) -> Reduce(r16), Some(TimesClass) -> Reduce(r16),  None -> Reduce(r16)),
/*15 */    Map(Some(PlusClass) -> Reduce(r17), Some(TimesClass) -> Reduce(r17),  None -> Reduce(r17)),
/*16 */    Map(Some(PlusClass) -> Reduce(r5), Some(TimesClass) -> Reduce(r13),  None -> Reduce(r5)),
/*17 */    Map(Some(NumClass) -> Reduce(r6), Some(IdClass) -> Reduce(r6)),
/*18 */    Map(Some(PlusClass) -> Reduce(r11), Some(TimesClass) -> Reduce(r11),  None -> Reduce(r11)),
/*19 */    Map(Some(NumClass) -> Reduce(r12), Some(IdClass) -> Reduce(r12))
  )
  val gotoTable: Vector[Map[Id, State]] = Vector(
/* 0 */   Map(1 -> 1, 2 -> 2, 6 -> 3, 3 -> 4, 4 -> 5, 5 -> 6, 7 -> 7, 11 -> 8, 8 -> 9, 9 -> 10, 10 -> 11, 12 -> 12, 13 -> 13),
/* 1 */   Map(),
/* 2 */   Map(),
/* 3 */   Map(),
/* 4 */   Map(),
/* 5 */   Map(6 -> 16, 7 -> 7, 11 -> 8, 10 -> 11, 9 -> 10, 8 -> 9, 12 -> 12, 13 -> 13),
/* 6 */   Map(),
/* 7 */   Map(),
/* 8 */   Map(),
/* 9 */   Map(),
/*10 */   Map(11 -> 18, 12 -> 12, 13 -> 13),
/*11 */   Map(),
/*12 */   Map(),
/*13 */   Map(),
/*14 */   Map(),
/*15 */   Map(),
/*16 */   Map(),
/*17 */   Map(),
/*18 */   Map(),
/*19 */   Map()
  )
  val handMaidParser = LR1Parser[Int](EmptyStack)(actionTable, gotoTable)

  "HandMaidParser" should "1 = 1" in {
    val result = handMaidParser(List(Num(1)).iterator)
    assert(result.getValue == Some(1))
  }

  it should "2 + 5 = 7" in {
    val result = handMaidParser(List(Num(2), Plus, Num(5)).iterator)
    assert(result.getValue == Some(7))
  }
  
  it should "4 + 3 + 8 = 15" in {
    val result = handMaidParser(List(Num(4), Plus, Num(3), Plus, Num(8)).iterator)
    assert(result.getValue == Some(15))
  }
  
  it should "2 * 3 = 6" in {
    val result = handMaidParser(List(Num(2), Times, Num(3)).iterator)
    assert(result.getValue == Some(6))
  }

  it should "4 * 3 * 7 = 84" in {
    val result = handMaidParser(List(Num(4), Times, Num(3), Times, Num(7)).iterator)
    assert(result.getValue == Some(84))
  }

  it should "3 * 5 + 4 = 19" in {
    val result = handMaidParser(List(Num(3), Times, Num(5), Plus, Num(4)).iterator)
    assert(result.getValue == Some(19))
  }

  it should "8 + 4 * 7 = 36" in {
    val result = handMaidParser(List(Num(8), Plus, Num(4), Times, Num(7)).iterator)
    assert(result.getValue == Some(36))
  }

  it should "7 + 1 * 6 + 3 = 16" in {
    val result = handMaidParser(List(Num(7), Plus, Num(1), Times, Num(6), Plus, Num(3)).iterator)
    assert(result.getValue == Some(16))
  }

   it should "7 * 2 + 4 * 1 * 6 + 3 = 41" in {
    val result = handMaidParser(List(Num(7), Times, Num(2), Plus, Num(4), Times, Num(1), Times, Num(6), Plus, Num(3)).iterator)
    assert(result.getValue == Some(41))
  }

  it should "fails for +" in {
    val result = handMaidParser(List(Plus).iterator)
    assert(result.getValue == None)
    result match {
      case UnexpectedToken(Plus, expected, rest) => 
        assert(expected == Set(NumClass, IdClass))
        assert(rest(List(Num(1)).iterator).getValue == Some(1))
      case _ => fail()
    }
  }

  it should "fails for 1 +" in {
    val result = handMaidParser(List(Num(1), Plus).iterator)
    assert(result.getValue == None)
    result match {
      case UnexpectedEnd(expected, rest) => 
        assert(expected == Set(NumClass, IdClass))
        assert(rest(List(Num(4)).iterator).getValue == Some(5))
      case _ => fail()
    }
  }

  it should "fails for 2 *" in {
    val result = handMaidParser(List(Num(2), Times).iterator)
    assert(result.getValue == None)
    result match {
      case UnexpectedEnd(expected, rest) => 
        assert(expected == Set(NumClass, IdClass))
        assert(rest(List(Num(4)).iterator).getValue == Some(8))
      case _ => fail()
    }
  }

  it should "fails for 2 + 5 *" in {
    val result = handMaidParser(List(Num(2), Plus, Num(5), Times).iterator)
    assert(result.getValue == None)
    result match {
      case UnexpectedEnd(expected, rest) => 
        assert(expected == Set(NumClass, IdClass))
        assert(rest(List(Num(3)).iterator).getValue == Some(17))
      case _ => fail()
    }
  }

  it should "fails for 3 + +" in {
    val result = handMaidParser(List(Num(3), Plus, Plus).iterator)
    assert(result.getValue == None)
    result match {
      case UnexpectedToken(Plus, expected, rest) => 
        assert(expected == Set(NumClass, IdClass))
        assert(rest(List(Num(4)).iterator).getValue == Some(7))
      case _ => fail()
    }
  }

  it should "fails for 3 * +" in {
    val result = handMaidParser(List(Num(3), Times, Plus).iterator)
    assert(result.getValue == None)
    result match {
      case UnexpectedToken(Plus, expected, rest) => 
        assert(expected == Set(NumClass, IdClass))
        assert(rest(List(Num(4)).iterator).getValue == Some(12))
      case _ => fail()
    }
  }

  it should "fails for 3 4" in {
    val result = handMaidParser(List(Num(3), Num(4)).iterator)
    assert(result.getValue == None)
    result match {
      case UnexpectedToken(Num(4), expected, rest) => 
        assert(expected == Set(PlusClass, TimesClass))
        assert(rest(Nil.iterator).getValue == Some(3))
      case _ => fail()
    }
  }
}


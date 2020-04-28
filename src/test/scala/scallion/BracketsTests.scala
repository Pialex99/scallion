package scallion

import org.scalatest._

import scallion.syntactic._

object BracketsTockens {
  sealed trait Tocken
  case object Open extends Tocken
  case object Close extends Tocken
}

import BracketsTockens._

class BracketsTests extends FlatSpec with Inside with Syntaxes with Operators with lr1.Parsing {

  type Kind = BracketsTockens.Tocken
  type Token = BracketsTockens.Tocken

  override def getKind(token: Token): Kind = identity(token)

  import scala.language.implicitConversions
  import LR1._
  import LR1.grammar._
  import LR1.stack._
  import LR1.item._

  implicit def implicitCast(t: BracketsTockens.Tocken): Syntax[Tocken] = elem(t)

  val res: Syntax[Int] = (Open ~ recursive(res) ~ Close).map{
    case _ ~ n ~ _ => n + 1
  } | epsilon(0)

  /*
    r0: 0 -> 1
    r1: 1 -> 𝛆_0
    r2: 1 -> 2
    r3: 2 -m> 3
    r4: 3 -> 4 Close
    r5: 4 -> Open 5
    r6: 5 -> 1
  */

  val r0 = NormalRule1(0, NonTerminal(1))
  val r1 = NormalRule0(1, 0)
  val r2 = NormalRule1(1, NonTerminal(2))
  val r3 = TransformRule[Int, Tocken ~ Int ~ Tocken](2, { case _ ~ n ~ _ => n + 1 }, NonTerminal(3))
  val r4 = NormalRule2(3, NonTerminal(4), Terminal(Close))
  val r5 = NormalRule2(4, Terminal(Open), NonTerminal(5))
  val r6 = NormalRule1(5, NonTerminal(1))

  val actionTable: Vector[Map[Option[Kind], Action]] = Vector(
/* 0 */ Map(None -> Reduce(r1), Some(Open) -> Shift(5)),
/* 1 */ Map(None -> Done),
/* 2 */ Map(None -> Reduce(r2)),
/* 3 */ Map(None -> Reduce(r3)),
/* 4 */ Map(Some(Close) -> Shift(6)),
/* 5 */ Map(Some(Close) -> Reduce(r1), Some(Open) -> Shift(5)),
/* 6 */ Map(None -> Reduce(r4)),
/* 7 */ Map(Some(Close) -> Reduce(r5)),
/* 8 */ Map(Some(Close) -> Reduce(r6)),
/* 9 */ Map(Some(Close) -> Reduce(r2)),
/*10 */ Map(Some(Close) -> Reduce(r3)),
/*11 */ Map(Some(Close) -> Shift(12)),
/*12 */ Map(Some(Close) -> Reduce(r4))
  )
  
  val gotoTable: Vector[Map[Id, State]] = Vector(
/* 0 */ Map(1 -> 1, 2 -> 2, 3 -> 3, 4 -> 4), 
/* 1 */ Map(),
/* 2 */ Map(),
/* 3 */ Map(),
/* 4 */ Map(),
/* 5 */ Map(5 -> 7, 1 -> 8, 2 -> 9, 3 -> 10, 4 -> 11),
/* 6 */ Map(),
/* 7 */ Map(),
/* 8 */ Map(),
/* 9 */ Map(),
/*10 */ Map(),
/*11 */ Map(),
/*12 */ Map()
  )

  val handMaidParser = LR1Parser[Int](EmptyStack)(actionTable, gotoTable)

  "HandmaisParser" should "output 0 on empty input" in {
    val result = handMaidParser(List().toIterator)
    assert(result.getValue == Some(0))
  }

  it should "() = 1" in {
    val result = handMaidParser(List(Open, Close).toIterator)
    assert(result.getValue == Some(1))
  }

  it should "(((()))) = 4" in {
    val result = handMaidParser(List(Open, Open, Open, Open, Close, Close, Close, Close).toIterator)
    assert(result.getValue == Some(4))
  }

  it should "fails for (" in {
    val result = handMaidParser(List(Open).iterator)
    assert(result.getValue == None)
    result match {
      case UnexpectedEnd(expected, rest) => 
        assert(expected == Set(Open, Close))
        assert(rest(List(Close).iterator).getValue == Some(1))
      case _ => fail()
    }
  }

  it should "fails for ())" in {
    val result = handMaidParser(List(Open, Close, Close).iterator)
    assert(result.getValue == None)
    result match {
      case UnexpectedToken(Close, expected, rest) => 
        assert(expected == Set())
        assert(rest(List().iterator).getValue == Some(1))
      case _ => fail()
    }
  }
}

package arithmetic

import scala.language.implicitConversions

import scallion.input._
import scallion.lexical._
import scallion.syntactic._

class ScallionParser extends Syntaxes with ll1.Parsing with gzpwd.Parsing with simplell1.Parsing with lr1.Parsing with cyk.Parsing with Operators {

  type Token = arithmetic.Token
  type Kind = TokenClass

  import Implicits._

  override def getKind(token: Token): TokenClass = token match {
    case NumberToken(value) => NumberClass
    case PlusToken => PlusClass
    case MinusToken => MinusClass
    case TimeToken => TimeClass
    case DivideToken => DivideClass
  }

  val numberValue: Syntax[Value] = accept(NumberClass) {
    case NumberToken(value) => NumberValue(value)
  }

  lazy val timeValue: Syntax[Value] = numberValue | recursive(timeValue ~ elem(TimeClass) ~ numberValue).map {
    case v1 ~ _ ~ v2 => TimeValue(v1, v2)
  }

  lazy val divideValue: Syntax[Value] = timeValue | recursive(divideValue ~ elem(DivideClass) ~ timeValue).map {
    case v1 ~ _ ~ v2 => DividValue(v1, v2)
  }

  lazy val plusValue: Syntax[Value] = divideValue | recursive(plusValue ~ elem(PlusClass) ~ divideValue).map {
    case v1 ~ _ ~ v2 => PlusValue(v1, v2)
  }
    
  lazy val minusValue: Syntax[Value] = plusValue | recursive(minusValue ~ elem(MinusClass) ~ plusValue).map {
    case v1 ~ _ ~ v2 => MinusValue(v1, v2)
  }

  lazy val ll1Syntax: Syntax[Value] = operators(numberValue) (
    elem(TimeClass) is LeftAssociative,
    elem(DivideClass) is LeftAssociative,
    elem(PlusClass) is LeftAssociative,
    elem(MinusClass) is LeftAssociative
  ) {
    case (n1, PlusToken, n2) => PlusValue(n1, n2)
    case (n1, MinusToken, n2) => MinusValue(n1, n2)
    case (n1, TimeToken, n2) => TimeValue(n1, n2)
    case (n1, DivideToken, n2) => DividValue(n1, n2)
  }

  lazy val lr1Syntax: Syntax[Value] = minusValue

  lazy val parser = LL1(ll1Syntax)

  lazy val lr1Parser = LR1(lr1Syntax)

  lazy val cykParser = CYK(lr1Syntax)

  def apply(it: Iterator[Token]): Option[Value] = parser(it).getValue

  def lr1Apply(it: Iterator[Token]): Option[Value] = lr1Parser(it).getValue
  
  def cykApply(it: Iterator[Token]): Option[Value] = cykParser(it).getValue
}
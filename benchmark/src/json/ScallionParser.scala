package json

import scala.language.implicitConversions

import scallion.input._
import scallion.lexical._
import scallion.syntactic._

class ScallionParser extends Syntaxes with ll1.Parsing with gzpwd.Parsing with simplell1.Parsing with lr1.Parsing with cyk.Parsing {

  type Token = json.Token
  type Kind = TokenClass

  import Implicits._

  override def getKind(token: Token): TokenClass = token match {
    case SeparatorToken(value, _) => SeparatorClass(value)
    case BooleanToken(_, _) => BooleanClass
    case NumberToken(_, _) => NumberClass
    case StringToken(_, _) => StringClass
    case NullToken(_) => NullClass
    case _ => NoClass
  }

  val booleanValue: Syntax[Value] = accept(BooleanClass) {
    case BooleanToken(value, range) => BooleanValue(value, range)
  }

  val numberValue: Syntax[Value] = accept(NumberClass) {
    case NumberToken(value, range) => NumberValue(value, range)
  }

  val stringValue: Syntax[StringValue] = accept(StringClass) {
    case StringToken(value, range) => StringValue(value, range)
  }

  val nullValue: Syntax[Value] = accept(NullClass) {
    case NullToken(range) => NullValue(range)
  }

  implicit def separator(char: Char): Syntax[Token] = elem(SeparatorClass(char))

  lazy val arrayValue: Syntax[Value] =
    ('[' ~ repsep(value, ',') ~ ']').map {
      case start ~ vs ~ end => ArrayValue(vs, (start.range._1, end.range._2))
    }

  lazy val binding: Syntax[(StringValue, Value)] =
    (stringValue ~ ':' ~ value).map {
      case key ~ _ ~ value => (key, value)
    }

  lazy val objectValue: Syntax[Value] =
    ('{' ~ repsep(binding, ',') ~ '}').map {
      case start ~ bs ~ end => ObjectValue(bs, (start.range._1, end.range._2))
    }

  lazy val value: Syntax[Value] = recursive {
    oneOf(
      arrayValue,
      objectValue,
      booleanValue,
      numberValue,
      stringValue.up[Value],
      nullValue)
  }

  lazy val parser = LL1(value)

  lazy val genParser = GZPWD(value)

  lazy val simpleParser = SimpleLL1(value)

  lazy val lr1Parser = LR1(value)

  lazy val cykParser = CYK(value)

  def apply(it: Iterator[Token]): Option[Value] = parser(it).getValue

  def genApply(it: Iterator[Token]): Option[Value] = genParser(it).getValue

  def simpleApply(it: Iterator[Token]): Option[Value] = simpleParser(it).getValue

  def lr1Apply(it: Iterator[Token]): Option[Value] = lr1Parser(it).getValue
  
  def cykApply(it: Iterator[Token]): Option[Value] = cykParser(it).getValue
}
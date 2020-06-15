package arithmetic

import scala.annotation._
import scala.collection.mutable.ArrayBuffer
import scala.util.Random

sealed abstract class Token
case class NumberToken(value: Double) extends Token
case object PlusToken extends Token
case object MinusToken extends Token
case object TimeToken extends Token
case object DivideToken extends Token
// case class BracketToken(open: Boolean) extends Token

sealed abstract class TokenClass(repr: String) {
  override def toString = repr
}
case object  NumberClass extends TokenClass("<number>")
case object PlusClass extends TokenClass("+")
case object MinusClass extends TokenClass("-")
case object TimeClass extends TokenClass("*")
case object DivideClass extends TokenClass("/")
// case class BracketClass(open: Boolean) extends TokenClass( if (open) "(" else ")" )

sealed abstract class Value 
case class NumberValue(value: Double) extends Value
case class PlusValue(left: Value, right: Value) extends Value
case class MinusValue(left: Value, right: Value) extends Value
case class TimeValue(left: Value, right: Value) extends Value
case class DividValue(left: Value, right: Value) extends Value

class ArithmeticGenerator(length: Int) extends Iterator[Token] {
  private val random = new Random(2020)
  private var currentLength = 0
  // private var openBrackets = 0
  private var needNumber = true
  
  override def hasNext: Boolean = needNumber || (currentLength /* + openBrackets */) < length

  override def next(): Token = {
    if (!hasNext) {
      throw new NoSuchElementException
    }
    currentLength += 1
    if (needNumber) {
      needNumber = false
      NumberToken(random.nextDouble())
    } else {
      needNumber = true
      random.nextInt(4) match {
        case 0 => PlusToken
        case 1 => MinusToken
        case 2 => TimeToken
        case 3 => DivideToken
      }
    }
  }
}
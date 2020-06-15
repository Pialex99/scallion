import scallion.syntactic._

object Grammars extends Syntaxes with ll1.Parsing with lr1.Parsing with cyk.Parsing {
  type Token = Char
  type Kind = Char

  override def getKind(token: Token): Kind = token

  import Implicits._

  def main(args: Array[String]) {
    println("Making LL(1) crash on not LL(1) language")
    lazy val s: Syntax[Unit] = recursive(elem('a') ~ s ~ a).map(_=>()) | epsilon(())
    lazy val a: Syntax[Unit] = (elem('a') ~ elem('b') ~ s).map(_=>()) | elem('c').map(_=>())
    try {
      LL1(s)
      println("No crash.")
    } catch {
      case _: LL1.ConflictException => 
        println("Crash as expected")
    }

    println("Using a LR(1) but not LL(1) language on LL(1)")
    lazy val x: Syntax[String] = recursive(elem('a') ~ x).map { case c ~ str => c + str } | x2
    lazy val x2: Syntax[String] = recursive(elem('a') ~ x2 ~ elem('b')).map { 
      case c1 ~ str ~ c2 => c1 + str + c2
    } | epsilon("")

    try {
      LL1(x)
      println("No crash.")
    } catch {
      case _: LL1.ConflictException => 
        println("Crash as expected")
    }

    println("Using the same gammar with LR(1)")
    try {
      LR1(x)
      println("No crash, as expected")
    } catch {
      case _: LR1.ConflictException =>
        println("Unexpected crash !")
    }

    lazy val p: Syntax[String] = recursive(elem('a') ~ p ~ elem('a') | elem('b') ~ p ~ elem('b')).map {
      case c ~ str ~ _ => c + str + c
    } | epsilon("")
    println("Not ambigous even length palindrom grammar")
    println("Is it LL(1) ?")
    try {
      LL1(p)
      println("No crash so yes (unexpected)")
    } catch {
      case _: LL1.ConflictException => 
        println("Crash so no (expected)")
    }

    println("Is it LR(1) ?")
    try {
      LR1(p)
      println("No crash so yes (unexpected)")
    } catch {
      case _: LR1.ConflictException => 
        println("Crash so no (expected)")
    }

    println("But CYK can handle it")
    assert(CYK(p).apply("abba".iterator).getValue == Some("abba"))

    lazy val sum: Syntax[Int] = recursive(sum ~ elem('+') ~ sum).map {
      case n1 ~ _ ~ n2 => n1 + n2
    } | accept('1') { case _ => 1 }
    println("Making LL(1) crash on ambiguous grammar")
    try {
      LL1(sum)
      println("No crash.")
    } catch {
      case _: LL1.ConflictException => 
        println("Crash as expected")
    }

    println("Making LR(1) crash on ambiguous grammar")
    try {
      LR1(sum)
      println("No crash.")
    } catch {
      case _: LR1.ConflictException => 
        println("Crash as expected")
    }

    println("Using CYK on ambiguous grammar")
    assert(CYK(sum).apply("1+1+1+1".iterator).getValue == Some(4))
  }
}
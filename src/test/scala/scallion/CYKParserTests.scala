package scallion

import org.scalatest._

import scallion.syntactic._

class CYKParserTests extends FlatSpec with Inside with Syntaxes with Operators with cyk.Parsing {

  type Kind = Boolean
  type Token = Int

  override def getKind(token: Token): Kind = token >= 0

  import CYK._
  "Elem" should "parse correctly when kind match" in {
    val parser = CYK(elem(true))
    inside(parser.apply(List(1).iterator)) {
      case Parsed(value, rest) => 
        assert(value == 1)
        inside(rest.apply(List(1).iterator)) {
          case UnexpectedEnd(rest) => 
            // does not work because the parser has consumed 2 tokens
            // inside(rest.apply(List().iterator)) {
            //   case Parsed(value, _) => 
            //     assert(value == 1)
            // }
        }
    }
    inside(parser.apply(List(42).iterator)) {
      case Parsed(value, _) => 
        assert(value == 42)
    }
  }

  it should "not parse correctly when kind mismatch" in {
    val parser = CYK(elem(true))
    inside(parser.apply(List(-1).iterator)) {
      case UnexpectedToken(token, rest) => 
        assert(token == -1)
        inside(rest.apply(List(1).iterator)) {
          case Parsed(value, _) => 
            assert(value == 1)
        }
    }
  }

  it should "fail for too long input" in {
    val parser = CYK(elem(true))
    inside(parser.apply(List(1, 2).iterator)) {
      case UnexpectedEnd(rest) => 
    }
  }

  "Success" should "return Parsed with empty iterator" in {
    val parser = CYK(epsilon(42))
    inside(parser.apply(List().iterator)) {
      case Parsed(value, _) => 
        assert(value == 42)
    }
  }

  it should "fail with not empty iterator" in {
    val parser = CYK(epsilon(42))
    inside(parser.apply(List(1).iterator)) {
      case UnexpectedToken(token, _) => 
        assert(token == 1)
    }
  }

  "Sequence" should "work with same kind" in {
    val parser = CYK(elem(true) ~ elem(true))
    inside(parser.apply(List(1, 2).iterator)) {
      case Parsed(value, _) => 
        assert(value == 1 ~ 2)
    }
  }

  it should "work with different kind" in {
    val parser = CYK(elem(false) ~ elem(true))
    inside(parser.apply(List(-1, 3).iterator)) {
      case Parsed(value, _) =>
        assert((-1) ~ 3 == value)
    }
    inside(parser.apply(List(1, -3).iterator)) {
      case UnexpectedEnd(rest) => 
    }
    inside(parser.apply(List(-3).iterator)) {
      case UnexpectedEnd(rest) => 
        inside(rest.apply(List(1).iterator)) {
          case Parsed(value, _) =>
            assert(value == (-3) ~ 1)
        }
    }
  }

  it should "work with nullable on left side" in {
    val parser = CYK(elem(true) ~ epsilon(6))
    inside(parser.apply(List(1).iterator)) {
      case Parsed(value, _) => 
        assert(value == 1 ~ 6)
    }
  }

  it should "work with nullable on right side" in {
    val parser = CYK(epsilon(42) ~ elem(false))
    inside(parser.apply(List(-4).iterator)) {
      case Parsed(value, _) => 
        assert(value == 42 ~ (-4))
    }
  }

  it should "work with both side nullable" in {
    val parser = CYK(epsilon(0) ~ epsilon(3))
    inside(parser.apply(List().iterator)) {
      case Parsed(value, _) => 
        assert(value == 0 ~ 3)
    }
  }

  "Disjunction" should "work for non abigious grammar" in {
    val parser = CYK(elem(true) | elem(false))
    inside(parser.apply(List(1).iterator)) {
      case Parsed(value, rest) => 
        assert(value == 1)
        inside(rest.apply(List(-1).iterator)) {
          case UnexpectedEnd(_) => 
        }
    }
    inside(parser.apply(List(-1).iterator)) {
      case Parsed(value, rest) => 
        assert(value == -1)
        inside(rest.apply(List(-1).iterator)) {
          case UnexpectedEnd(_) => 
        }
    }
  }

  it should "work with nullable left side" in {
    val parser = CYK(epsilon(3) | elem(false))
    inside(parser.apply(List().iterator)) {
      case Parsed(value, rest) => 
        assert(value == 3)
        inside(rest.apply(List(-2).iterator)) {
          case Parsed(value, _) => 
            assert(value == -2)
        }
    }
    inside(parser.apply(List(-3).iterator)) {
      case Parsed(value, rest) => 
        assert(value == -3)
        inside(rest.apply(List().iterator)) {
          case Parsed(value, rest) => 
            assert(value == -3)
        }
    }
  }

  it should "work with nullable right side" in {
    val parser = CYK(elem(false) | epsilon(42))
    inside(parser.apply(List().iterator)) {
      case Parsed(value, rest) => 
        assert(value == 42)
        inside(rest.apply(List(-2).iterator)) {
          case Parsed(value, _) => 
            assert(value == -2)
        }
    }
    inside(parser.apply(List(-3).iterator)) {
      case Parsed(value, rest) => 
        assert(value == -3)
        inside(rest.apply(List().iterator)) {
          case Parsed(value, rest) => 
            assert(value == -3)
        }
    }
  }

  "Transform" should "work with elem inner syntax" in {
    val parser = CYK(accept(true){ case n => n * 4 })
    inside(parser.apply(List(2).iterator)) {
      case Parsed(value, _) => 
        assert(value == 2 * 4)
    }
  }

  it should "work with nullable inner syntax" in {
    val parser = CYK(epsilon(42).map(_ / 6)) 
    inside(parser.apply(List().iterator)) {
      case Parsed(value, _) => 
        assert(value == 7)
    }
    inside(parser.apply(List(1).iterator)) {
      case UnexpectedToken(token, rest) => 
        assert(token == 1)
    }
  }

  it should "work with nullable disjunction inner syntax" in {
    val parser = CYK((elem(true) | epsilon(3)).map(_ * 4))
    inside(parser.apply(List().iterator)) {
      case Parsed(value, rest) => 
        assert(value == 12)
    }
    inside(parser.apply(List(4).iterator)) {
      case Parsed(value, rest) => 
        assert(value == 16)
    }
  }

  it should "return a value with anbigious grammar" in {
    val parser = CYK(accept(true){ case n => n + 4} | accept(true){ case n => n - 2 })
    inside(parser.apply(List(3).iterator)) {
      case Parsed(value, rest) => 
        assert(value == 1 || value == 5)
    }
  }

  "Recursive" should "return first value with infinite left recursion" in {
    lazy val s: Syntax[Int] = elem(true) | epsilon(0) | recursive(s).map(_ + 1)
    val parser = CYK(s)
    inside(parser.apply(List(1).iterator)) {
      case Parsed(value, rest) => 
        assert(value == 1)
    }
    inside(parser.apply(Nil.iterator)) {
      case Parsed(value, rest) => 
        assert(value == 0)
    }
  }
  
  "Special syntax" should "work" in {
    val n: Syntax[List[Int]] = accept(true) { case i => i::Nil }
    lazy val a: Syntax[List[Int]] = (b ~ n) map { case xs ~ x => xs ::: x}
    lazy val b: Syntax[List[Int]] = n | recursive(a)
    lazy val s: Syntax[List[Int]] = recursive(a)
    val parser = CYK(s)
    inside(parser.apply(List(1, 2, 3, 4).iterator)) {
      case Parsed(value, _) => 
        assert(value == List(1, 2, 3, 4))
    }
  }

  "Infinit sytax" should "be parsed with a single elem" in {
    lazy val s: Syntax[Int] = epsilon(0) | recursive(s).map(_ + 1)
    val parser = CYK(s)
    inside(parser.apply(List().iterator)) {
      case Parsed(values, _) => 
        assert(values == 0)
    }
  }
}
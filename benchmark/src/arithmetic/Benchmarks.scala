package arithmetic

import org.scalameter.api._
import org.scalameter.CurveData
import org.scalameter.picklers.Implicits._
import org.scalameter.utils.Tree

abstract class BenchmarkTokens extends Bench.OfflineReport {
  val sizes = Gen.enumeration("size")(
    // 10000
    100000,
    200000,
    300000,
    400000,
    500000,
    600000,
    700000,
    800000,
    900000,
    1000000
  )
  val tokens = for {
    length <- sizes
  } yield new ArithmeticGenerator(length).toArray
}

// class SimpleLL1PWD extends BenchmarkTokens {
//   performance of "Simple LL(1) Parsing with Derivatives" in {
//     measure method "parse" in {
//       using(tokens) in { ts =>

//         // Note that we filter out files with more than 100'000 tokens,
//         // as the parser takes very long and most likely will fail
//         // due to a stack overflow.
//         // The stack overflow is check in Crashes.
//         if (ts.size <= 100000) {
//           val parser = new ScallionParser
//           assert(parser.simpleApply(ts.toIterator).nonEmpty)
//         }
//       }
//     }
//   }
// }

class ZippyLL1PWD extends BenchmarkTokens {
  performance of "Zippy LL(1) Parsing with Derivatives" in {
    measure method "parse" in {
      using(tokens) in { ts =>
        val parser = new ScallionParser
        assert(parser.apply(ts.toIterator).nonEmpty)
      }
    }
  }
}

// class ZippyGenPWD extends BenchmarkTokens {
//   performance of "Zippy (Generalized) Parsing with Derivatives" in {
//     measure method "parse" in {
//       using(tokens) in { ts =>
//         val parser = new ScallionParser
//         assert(parser.genApply(ts.toIterator).nonEmpty)
//       }
//     }
//   }
// }

class LR1 extends BenchmarkTokens {
  performance of "LR1 Parsing" in {
    measure method "parse" in {
      using(tokens) in { ts =>
        val parser = new ScallionParser
        assert(parser.lr1Apply(ts.toIterator).nonEmpty)
      }
    }
  } 
}

class CYK extends BenchmarkTokens {
  performance of "CYK Parsing" in {
    measure method "parse" in {
      using(tokens) in { ts =>
        val parser = new ScallionParser
        assert(parser.cykApply(ts.toIterator).nonEmpty)
      }
    }
  } 
}

// class EndToEndBenchmarks extends BenchmarkFiles {

//   performance of "JSON end-to-end parsing" in {

//     measure method "Scallion parse" in {
//       using(files) in { file =>
//         val tokens = JSONLexer(io.Source.fromFile("benchmark/resources/" + file + ".json"))
//         val parser = new ScallionParser
//         assert(parser(tokens).nonEmpty)
//       }
//     }

//     measure method "ANTLR parse" in {
//       import org.antlr.v4.runtime._
//       using(files) in { file =>
//         val lexer = new json.antlr.JSONLexer(CharStreams.fromFileName("benchmark/resources/" + file + ".json"))
//         val parser = new json.antlr.JSONParser(new CommonTokenStream(lexer))
//         parser.json()
//       }
//     }
//   }
// }

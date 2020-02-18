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

import Tokens._

class LR1ParserTests extends ParserTests with lr1.LR1Parsing {
  import LR1._
  import SafeImplicits._

  override def builder[A](syntax: Syntax[A]): Parser[A] = LR1(syntax)
  
  // elem

  // accept

  // failure

  // sequencing

  // concatenation

  // disjunction

  // tagged disjunction

  // many

  // many1

  // recursive

  // LR1 conflicts

  import LR1Conflict._

}

/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module Helper {
  /************
   Definitions
  ************/

  function SeqToString<T>(xs: seq<T>, printer: T -> string): string {
    if |xs| == 0 then
      ""
    else
      printer(xs[0]) + SeqToString(xs[1..], printer)
  }

  /*******
   Lemmas
  *******/

  lemma Congruence<T, U>(x: T, y: T, f: T -> U)
    requires x == y
    ensures f(x) == f(y)
  {}
}

/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module Helper {
  /************
   Definitions
  ************/

  function ArrayToSeq<T>(a: array<T>): (xs: seq<T>)
    reads a
    ensures a.Length == |xs|
  {
    a[..]
  }

  function SeqToString<T>(xs: seq<T>, printer: T -> string): string {
    if |xs| == 0 then
      ""
    else
      printer(xs[0]) + SeqToString(xs[1..], printer)
  }

  function NatToString(n: nat): string {
    match n
    case 0 => "0" case 1 => "1" case 2 => "2" case 3 => "3" case 4 => "4"
    case 5 => "5" case 6 => "6" case 7 => "7" case 8 => "8" case 9 => "9"
    case _ => NatToString(n / 10) + NatToString(n % 10)
  }

  /*******
   Lemmas
  *******/

  lemma Congruence<T, U>(x: T, y: T, f: T -> U)
    requires x == y
    ensures f(x) == f(y)
  {}

  // TODO: try to prove
  lemma {:axiom} ArrayToSeqIsInjective<T>(a: array<T>, b: array<T>)
    requires a != b
    ensures ArrayToSeq(a) != ArrayToSeq(b)

}

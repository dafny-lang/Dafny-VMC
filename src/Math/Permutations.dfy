/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module Permutations {
  import NatArith

  /************
   Definitions
  ************/
  
  function NumberOfPermutationsOf<T(==)>(s: seq<T>): nat {
    |CalculateAllPermutationsOf(s)|
  }

  function CalculateAllPermutationsOf<T(==)>(s: seq<T>): (x: set<seq<T>>)
    ensures forall p | p in x :: |p| == |s|
  {
    if |s| == 0 then
      {s}
    else
      set p, i | p in CalculateAllPermutationsOf(s[1..]) && 0 <= i <= |s|-1 :: InsertAt(p, s[0], i)
  }

  function InsertAt<T>(s: seq<T>, x: T, i: nat): seq<T>
    requires i <= |s|
  {
    s[..i] + [x] + s[i..]
  }

}
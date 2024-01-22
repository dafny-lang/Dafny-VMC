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

  function Swap<T>(s: seq<T>, i: nat, j: nat): (t: seq<T>)
    requires i <= j
    requires 0 <= i < |s|
    requires 0 <= j < |s|
    ensures |s| == |t|
  {
    if i == j then 
      s 
    else 
      s[..i] + [s[j]] + s[i+1..j] + [s[i]] + s[j+1..]
  }

  /*******
   Lemmas
  *******/

  lemma CalculateAllPermutationsOfIsNonEmpty<T>(s: seq<T>)
    ensures s in CalculateAllPermutationsOf(s)
    ensures NumberOfPermutationsOf(s) > 0
  {
    assert s in CalculateAllPermutationsOf(s) by {
      if |s| == 0 {
      } else {
        assert s[1..] in CalculateAllPermutationsOf(s[1..]) by {
          CalculateAllPermutationsOfIsNonEmpty(s[1..]);
        }
        assert InsertAt(s[1..], s[0], 0) == s;
      }
    }
  }
}
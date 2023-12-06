/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

 module Permutations {

  /************
   Definitions
  ************/

  predicate IsPermutationOf<T(==)>(p: seq<T>, s: seq<T>) {
    multiset(p) == multiset(s)
  }

  ghost function AllPermutationsOf<T(!new)>(s: seq<T>): iset<seq<T>> {
    iset p | IsPermutationOf(p, s)
  }

  function CalculateAllPermutationsOf<T(==)>(s: seq<T>): set<seq<T>> {
    if |s| == 0 then
      {s}
    else
      set p, i | p in CalculateAllPermutationsOf(s[1..]) && 0 <= i <= |p| :: InsertAt(p, s[0], i)
  }

  function InsertAt<T>(s: seq<T>, x: T, i: nat): seq<T>
    requires i <= |s|
  {
    s[..i] + [x] + s[i..]
  }

  function DeleteAt<T>(s: seq<T>, i: nat): seq<T>
    requires i < |s|
  {
    s[..i] + s[i+1..]
  }

  function FirstOccurrence<T(==)>(p: seq<T>, x: T): (i: nat)
    requires x in multiset(p)
    ensures i < |p|
    ensures p[i] == x
  {
    if p[0] == x then
      0
    else
      FirstOccurrence(p[1..], x) + 1
  }

  /*******
   Lemmas
  *******/

  lemma Correctness<T(!new)>(s: seq<T>)
    ensures (iset p | p in CalculateAllPermutationsOf(s)) == AllPermutationsOf(s)
  {
    assert (iset p | p in CalculateAllPermutationsOf(s)) == AllPermutationsOf(s) by {
      assert forall p :: p in CalculateAllPermutationsOf(s) <==> p in AllPermutationsOf(s) by {
        forall p
          ensures p in CalculateAllPermutationsOf(s) <==> p in AllPermutationsOf(s) 
          {
            CorrectnessImplicationOne(s, p);
            CorrectnessImplicationTwo(s, p);
          }
      }
    }
  }

  lemma CorrectnessImplicationOne<T(!new)>(s: seq<T>, p: seq<T>)
    ensures p in CalculateAllPermutationsOf(s) ==> p in AllPermutationsOf(s)
  {
    if |s| == 0 {
      // induction base, no proof hints needed
    } else {
      // induction step
      if p in CalculateAllPermutationsOf(s) {
        assert p in AllPermutationsOf(s) by {
          assert IsPermutationOf(p, s) by {
            var p', i :| p' in CalculateAllPermutationsOf(s[1..]) && 0 <= i <= |p'| && p == InsertAt(p', s[0], i);
            calc == {
              multiset(p);
              multiset(InsertAt(p', s[0], i));
              { MultisetAfterInsertAt(p', s[0], i); }
              multiset([s[0]]) + multiset(p');
              { CorrectnessImplicationOne(s[1..], p'); } // induction hypothesis
              multiset([s[0]]) + multiset(s[1..]);
              multiset([s[0]] + s[1..]);
              { assert [s[0]] + s[1..] == s; }
              multiset(s);
            }
          }
        }
      }
    }
  }

  lemma CorrectnessImplicationTwo<T(!new)>(s: seq<T>, p: seq<T>)
    ensures p in CalculateAllPermutationsOf(s) <== p in AllPermutationsOf(s)
  {
    if |s| == 0 {
      // induction base, no proof hints needed
    } else {
      // induction step
      if p in AllPermutationsOf(s) {
        assert p in CalculateAllPermutationsOf(s) by {
          var i := FirstOccurrence(p, s[0]);
          var p' := DeleteAt(p, i);
          assert p' in CalculateAllPermutationsOf(s[1..]) by {
            assert p' in AllPermutationsOf(s[1..]) by {
              PermutationBeforeAndAfterDeletionAt(p, s, i, 0);
            }
            CorrectnessImplicationTwo(s[1..], p'); // induction hypothesis
          }
          assert p == InsertAt(p', s[0], i) by {
            InsertAfterDeleteAt(p, i);
          }
        }
      }
    }
  }

  lemma MultisetAfterInsertAt<T>(s: seq<T>, x: T, i: nat)
    requires i <= |s|
    ensures multiset(InsertAt(s, x, i)) == multiset([x]) + multiset(s)
  {
    calc == {
      multiset(InsertAt(s, x, i));
      multiset(s[..i] + [x] + s[i..]);
      multiset(s[..i]) + multiset([x]) + multiset(s[i..]);
      multiset([x]) + multiset(s[..i]) + multiset(s[i..]);
      multiset([x]) + multiset(s[..i] + s[i..]);
      { assert s[..i] + s[i..] == s; }
      multiset([x]) + multiset(s);
    }
  }

  lemma PermutationBeforeAndAfterDeletionAt<T>(p: seq<T>, s: seq<T>, i: nat, j: nat)
    requires IsPermutationOf(p, s)
    requires i < |p|
    requires j < |s|
    requires p[i] == s[j]
    ensures IsPermutationOf(DeleteAt(p, i), DeleteAt(s, j))
  {
    assert IsPermutationOf(DeleteAt(p, i), DeleteAt(s, j)) by {
      calc == {
        multiset(DeleteAt(p, i));
        multiset(p[..i] + p[i+1..]);
        multiset(p[..i]) + multiset(p[i+1..]);
        multiset(p[..i]) + multiset([p[i]]) + multiset(p[i+1..]) - multiset([p[i]]);
        multiset(p[..i] + [p[i]] + p[i+1..]) - multiset([p[i]]);
        { assert p[..i] + [p[i]] + p[i+1..] == p; }
        multiset(p) - multiset([p[i]]);
        multiset(s) - multiset([s[j]]);
        { assert s[..j] + [s[j]] + s[j+1..] == s; }
        multiset(s[..j] + [s[j]] + s[j+1..]) - multiset([s[j]]);
        multiset(s[..j]) + multiset([s[j]]) + multiset(s[j+1..]) - multiset([s[j]]);
        multiset(s[..j]) + multiset(s[j+1..]);
        multiset(s[..j] + s[j+1..]);
        multiset(DeleteAt(s, j));
      }
    }
  }

  lemma InsertAfterDeleteAt<T>(s: seq<T>, i: nat)
    requires i < |s|
    ensures s == InsertAt(DeleteAt(s, i), s[i], i)
  {}

  lemma CalculateAllPermutationsOfIsNonEmpty<T(==)>(s: seq<T>)
    ensures s in CalculateAllPermutationsOf(s)
    ensures |CalculateAllPermutationsOf(s)| > 0
  {
    assert s in CalculateAllPermutationsOf(s) by {
      if |s| == 0 {
      } else {
        assert s[1..] in CalculateAllPermutationsOf(s[1..]) by {
          CalculateAllPermutationsOfIsNonEmpty(s[1..]);
        }
        assert  InsertAt(s[1..], s[0], 0) == s;
      }
    }
  }
}
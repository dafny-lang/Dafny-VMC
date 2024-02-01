/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module FisherYates.Implementation {
  import Interface
  import Monad
  import Model
  import Uniform

  trait {:termination false} Trait extends Interface.Trait {

    method {:vcs_split_on_every_assert} Shuffle<T>(a: array<T>)
      decreases *
      modifies `s, a
      ensures Model.Shuffle(old(a[..]))(old(s)) == Monad.Result(a[..], s)
    {
      ghost var prevASeq := a[..];
      ghost var prevI := 0;
      ghost var prevS := s;
      if a.Length > 1 {
        var i := 0;
        while i < a.Length - 1
          decreases a.Length - 1 - i
          invariant prevI == if i == 0 then i else i - 1
          invariant prevI <= |prevASeq|
          invariant i <= |a[..]|
          invariant i <= a.Length - 1
          invariant |prevASeq| == |a[..]| == a.Length
          invariant Model.Shuffle(old(a[..]))(old(s)) == Model.Shuffle(prevASeq, prevI)(prevS)
          invariant Model.Shuffle(prevASeq, prevI)(prevS) == Model.Shuffle(a[..], i)(s)
        {
          prevI := i;
          prevASeq := a[..];
          prevS := s;
          var j := UniformIntervalSample(i, a.Length);
          assert prevASeq == a[..];
          Swap(a, i, j);
          i := i + 1;
          assert Model.Shuffle(prevASeq, prevI)(prevS) == Model.Shuffle(a[..], i)(s) by {
            calc {
              Model.Shuffle(prevASeq, prevI)(prevS);
              Model.Shuffle(Model.Swap(prevASeq, prevI, Uniform.Model.IntervalSample(prevI, |prevASeq|)(prevS).value), prevI + 1)(Uniform.Model.IntervalSample(prevI, |prevASeq|)(prevS).rest);
              { assert Uniform.Model.IntervalSample(prevI, |prevASeq|)(prevS).value == j;
                assert Uniform.Model.IntervalSample(prevI, |prevASeq|)(prevS).rest == s; }
              Model.Shuffle(Model.Swap(prevASeq, prevI, j), prevI + 1)(s);
              { assert i == prevI + 1;
                assert Model.Swap(prevASeq, prevI, j) == a[..];
              }
              Model.Shuffle(a[..], i)(s);
            }
          }
        }

        assert Model.Shuffle(old(a[..]))(old(s)) == Monad.Result(a[..], s) by {
          assert i == a.Length - 1;
          calc {
            Model.Shuffle(old(a[..]))(old(s));
            Model.Shuffle(prevASeq, prevI)(prevS);
            Model.Shuffle(a[..], i)(s);
            Monad.Return(a[..])(s);
            Monad.Result(a[..], s);
          }
        }

      }
    }

    method Swap<T>(a: array<T>, i: nat, j: nat)
      modifies a
      requires i <= j
      requires 0 <= i < a.Length
      requires 0 <= j < a.Length
      ensures Model.Swap(old(a[..]), i, j) == a[..]
      ensures old(s) == s
    {
      a[i], a[j] := a[j], a[i];
    }

  }
}
/*******************************************************************************
*  Copyright by the contributors to the Dafny Project
*  SPDX-License-Identifier: MIT
*******************************************************************************/

include "../../ProbabilisticProgramming/Monad.dfy"
include "Interface.dfy"

module GeometricImplementation {
  import opened Monad
  import opened GeometricInterface

  trait {:termination false} Geometric extends IGeometric {

    method Geometric() returns (c: nat)
      modifies this
      decreases *
      ensures !old(s)(c)
      ensures forall i | 0 <= i < c :: old(s)(i)
      ensures s == IterateTail(old(s), c + 1)
    {
      c := 0;
      var b := Coin();
      assert old(s)(c) == b;
      assert s == IterateTail(old(s), c + 1);
      while b
        decreases *
        invariant s == IterateTail(old(s), c + 1)
        invariant b == IterateTail(old(s), c)(0)
        invariant b == old(s)(c)
        invariant forall i | 0 <= i < c :: old(s)(i)
      {
        var s' := s;
        var c' := c;
        var b' := b;
        assert forall i | 0 <= i < c' :: old(s)(i);
        assert s' == IterateTail(old(s), c' + 1);
        assert b' == IterateTail(old(s), c')(0);
        b := Coin();
        assert (b, s) == (Head(s'), Tail(s'));
        assert b == IterateTail(old(s), c' + 1)(0);
        assert s == Tail(IterateTail(old(s), c' + 1));
        TailOfIterateTail(old(s), c' + 1);
        assert s == IterateTail(old(s), (c' + 1) + 1);
        c := c + 1;
        assert c == c' + 1;
        assert old(s)(c') by {
          assert b';
        }
        assert s == IterateTail(old(s), c + 1);
        assert b == IterateTail(old(s), c)(0);
      }
    }

  }
}

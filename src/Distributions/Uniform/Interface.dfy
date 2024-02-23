/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module Uniform.Interface {
  import Monad
  import Model
  import Pos
  import Rand

  trait {:termination false} Trait {

    ghost var s: Rand.Bitstream

    method UniformSample(n: Pos.pos) returns (u: nat)
      modifies `s
      decreases *
      ensures u < n
      ensures Model.Sample(n)(old(s)) == Monad.Result(u, s)

    method UniformIntervalSample(a: int, b: int) returns (u: int)
      modifies `s
      decreases *
      requires a < b
      ensures a <= u < b
      ensures Model.IntervalSample(a, b)(old(s)) == Monad.Result(u, s)
    {
      var v := UniformSample(b - a);
      assert Model.Sample(b-a)(old(s)) == Monad.Result(v, s);
      assert Model.IntervalSample(a, b)(old(s)) == Monad.Result(a + v, s);
      u := a + v;
    }

  }
}

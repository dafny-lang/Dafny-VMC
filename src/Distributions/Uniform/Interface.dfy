/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module Uniform.Interface {
  import UniformPowerOfTwo
  import Monad
  import Coin
  import Model
  import Pos

  trait {:termination false} Trait extends UniformPowerOfTwo.Interface.Trait {

    method UniformSample(n: Pos.pos) returns (o: nat)
      modifies `s
      decreases *
      requires n > 0
      ensures o < n
      ensures Model.Sample(n)(old(s)) == Monad.Result(o, s)

    method UniformIntervalSample(a: int, b: int) returns (o: int)
      modifies `s
      decreases *
      requires a < b
      ensures a <= o < b
      ensures Model.IntervalSample(a, b)(old(s)) == Monad.Result(o, s)
    {
      var v := UniformSample(b - a);
      assert Model.Sample(b-a)(old(s)) == Monad.Result(v, s);
      assert Model.IntervalSample(a, b)(old(s)) == Monad.Result(a + v, s);
      o := a + v;
    }

  }
}

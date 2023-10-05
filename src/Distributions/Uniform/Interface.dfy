/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

include "../Coin/Coin.dfy"
include "../UniformPowerOfTwo/UniformPowerOfTwo.dfy"
include "Model.dfy"

module Uniform.Interface {
  import Coin
  import Model
  import UniformPowerOfTwo

  trait {:termination false} Trait extends Coin.Interface.Trait, UniformPowerOfTwo.Interface.Trait {

    method UniformSample(n: nat) returns (u: nat)
      modifies this
      decreases *
      requires n > 0
      ensures u < n
      ensures Model.Sample(n)(old(s)) == (u, s)

    method UniformIntervalSample(a: int, b: int) returns (u: int)
      modifies this
      decreases *
      requires a < b
      ensures a <= u < b
      ensures Model.IntervalSample(a, b)(old(s)) == (u, s)
    {
      var v := UniformSample(b - a);
      assert Model.Sample(b-a)(old(s)) == (v, s);
      assert Model.IntervalSample(a, b)(old(s)) == (a + v, s);
      u := a + v;
    }

  }
}

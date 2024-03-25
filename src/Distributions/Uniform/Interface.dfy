/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module Uniform.Interface {
  import Monad
  import Model
  import opened Pos
  import Bitstream

  trait {:termination false} Trait extends Bitstream.Interface.Trait {

    method UniformSample(n: pos) returns (u: nat)
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

  trait {:termination false} Trait32 extends Bitstream.Interface.Trait {

    method UniformSample32(n: pos32) returns (u: nat32)
      modifies `s
      decreases *
      ensures u < n
      ensures Model.Sample(n as nat)(old(s)) == Monad.Result(u as nat, s)

    method UniformIntervalSample32<T>(a: int32, b: int32, ghost arr: array<T>) returns (u: int32)
      modifies `s
      decreases *
      requires 0 < b as int - a as int < 0x8000_0000
      ensures a <= u < b
      ensures Model.IntervalSample(a as int, b as int)(old(s)) == Monad.Result(u as int, s)
      ensures old(arr[..]) == arr[..]
    {
      var v := UniformSample32(b-a);
      assert Model.Sample(b as int - a as int)(old(s)) == Monad.Result(v as nat, s);
      assert Model.IntervalSample(a as int, b as int)(old(s)) == Monad.Result(a as int + v as int, s);
      u := a + v;
    }

  }

}

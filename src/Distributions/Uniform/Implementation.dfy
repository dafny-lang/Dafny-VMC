/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module Uniform.Implementation {
  import UniformPowerOfTwo
  import Interface
  import opened Pos

  trait {:termination false} Trait extends Interface.Trait {

    method {:verify false} UniformSample (n: Pos.pos)
      returns (o: nat)
      modifies this
      decreases *
    {
      var x := UniformPowerOfTwoSample(2 * n);
      while ! (x < n)
        decreases *
      {
        x := UniformPowerOfTwoSample(2 * n);
      }
      var r := x;
      o := r;
    }

  }
}

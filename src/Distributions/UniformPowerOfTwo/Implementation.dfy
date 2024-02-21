/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module UniformPowerOfTwo.Implementation {
  import Monad
  import Model
  import Interface

  trait {:termination false} Trait extends Interface.Trait {
    method UniformPowerOfTwoSample(n: nat) returns (u: nat)
      requires n >= 1
      modifies `s
      ensures Model.Sample(n)(old(s)) == Monad.Result(u, s)

  }
}

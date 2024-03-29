/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module UniformPowerOfTwo.Interface {
  import Bitstream

  trait {:termination false} Trait extends Bitstream.Interface.Trait {

    // The return value u is uniformly distributed between 0 <= u < 2^k where 2^k <= n < 2^(k + 1).
    method UniformPowerOfTwoSample(n: nat) returns (u: nat)
      requires n >= 1
      modifies `s

  }
}
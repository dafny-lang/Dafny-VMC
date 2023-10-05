/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

include "../Coin/Coin.dfy"
include "Model.dfy"

module UniformPowerOfTwo.Interface {
  import Coin
  import Model

  trait {:termination false} Trait extends Coin.Interface.Trait {

    // The return value u is uniformly distributed between 0 <= u < 2^k where 2^k <= n < 2^(k + 1).
    method UniformPowerOfTwoSample(n: nat) returns (u: nat)
      requires n >= 1
      modifies this
      ensures Model.Sample(n)(old(s)) == (u, s)

  }
}

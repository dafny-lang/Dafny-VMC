/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

include "../Coin/Coin.dfy"
include "Model.dfy"

module UniformPowerOfTwoInterface {
  import Coin
  import Model = UniformPowerOfTwoModel

  trait {:termination false} Trait extends Coin.Interface.Trait {

    method UniformPowerOfTwoSample(n: nat) returns (u: nat)
      modifies this
      ensures Model.UniformPowerOfTwoSample(n)(old(s)) == (u, s)

  }
}

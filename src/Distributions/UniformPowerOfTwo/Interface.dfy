/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

include "../Coin/Coin.dfy"
include "Model.dfy"

module Interface {
  import Coin
  import Model

  trait {:termination false} Trait extends Coin.Interface.Trait {

    method UniformPowerOfTwoSample(n: nat) returns (u: nat)
      modifies this
      ensures Model.Sample(n)(old(s)) == (u, s)

  }
}

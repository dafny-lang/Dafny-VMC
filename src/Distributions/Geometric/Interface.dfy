/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

include "../../ProbabilisticProgramming/Monad.dfy"
include "../Coin/Coin.dfy"
include "Model.dfy"

module GeometricInterface {
  import Coin
  import Monad
  import Model = GeometricModel

  trait {:termination false} Trait extends Coin.Interface.Trait {

    method GeometricSample() returns (c: nat)
      modifies this
      decreases *
      ensures Model.Sample()(old(s)) == (c, s)

  }
}
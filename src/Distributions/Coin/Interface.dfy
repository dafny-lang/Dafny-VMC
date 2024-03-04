/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module Coin.Interface {
  import Monad
  import Rand
  import Model
  import UniformPowerOfTwo

  trait {:termination false} Trait extends UniformPowerOfTwo.Interface.Trait {

    method CoinSample() returns (b: bool)
      modifies `s
      ensures Model.Sample(old(s)) == Monad.Result(b, s)

  }
}
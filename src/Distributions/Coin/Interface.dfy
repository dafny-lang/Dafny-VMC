/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module Coin.Interface {
  import Monad
  import Rand
  import Model
  import Uniform

  trait {:termination false} Trait extends Uniform.Interface.Trait {

    method CoinSample() returns (b: bool)
      modifies `s
      decreases *
      ensures Model.Sample(old(s)) == Monad.Result(b, s)

  }
}

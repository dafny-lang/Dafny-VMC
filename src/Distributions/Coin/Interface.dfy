/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module Coin.Interface {
  import Monad
  import Rand
  import Model

  method {:extern "Coin_mInterface.DRandomCoin", "Coin"} ExternCoinSample() returns (b: bool)

  trait {:termination false} Trait {
    ghost var s: Rand.Bitstream

    method CoinSample() returns (b: bool)
      modifies this
      ensures Model.Sample(old(s)) == Monad.Result(b, s)
    {
      b := ExternCoinSample();
      assume {:axiom} false; // assume correctness of extern implementation
    }

  }
}

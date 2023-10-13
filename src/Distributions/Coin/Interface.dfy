/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module Coin.Interface {
  import Rand
  import Model

  method {:extern "DRandomCoin", "Coin"} ExternCoinSample() returns (b: bool)

  trait {:termination false} Trait {
    ghost var s: Rand.Bitstream

    method CoinSample() returns (b: bool)
      modifies this
      ensures Model.Sample(old(s)) == (b, s)
    {
      b := ExternCoinSample();
      assume {:axiom} false; // assume correctness of extern implementation
    }

  }
}

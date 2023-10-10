/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module Coin.Interface {
  import Partials
  import RandomNumberGenerator
  import Model

  method {:extern "DRandomCoin", "Coin"} ExternCoinSample() returns (b: bool)

  trait {:termination false} Trait {
    ghost var s: RandomNumberGenerator.RNG

    method CoinSample() returns (b: bool)
      modifies this
      ensures Model.Sample(old(s)) == Partials.Terminating((b, s))
    {
      b := ExternCoinSample();
      assume {:axiom} false; // assume correctness of extern implementation
    }

  }
}

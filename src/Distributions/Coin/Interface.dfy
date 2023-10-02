/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

include "../../ProbabilisticProgramming/RandomNumberGenerator.dfy"
include "Model.dfy"

module CoinInterface {
  import RandomNumberGenerator
  import Model = CoinModel

  method {:extern "DRandomCoin", "Coin"} ExternCoinSample() returns (b: bool)
  
  trait {:termination false} Trait {
    ghost var s: RandomNumberGenerator.RNG

    method CoinSample() returns (b: bool)
      modifies this
      ensures Model.CoinSample(old(s)) == (b, s)
    {
      b := ExternCoinSample();
      assume {:axiom} false;
    }

  }
}

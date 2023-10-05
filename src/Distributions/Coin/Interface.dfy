/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

include "../../ProbabilisticProgramming/RandomNumberGenerator.dfy"
include "Model.dfy"

module CoinExtern {

  method {:extern "DRandomCoin", "Coin"} ExternCoinSample() returns (b: bool)

}

module Coin.Interface {
  import RandomNumberGenerator
  import Model
  import CoinExtern

  trait {:termination false} Trait {
    ghost var s: RandomNumberGenerator.RNG

    method CoinSample() returns (b: bool)
      modifies this
      ensures Model.Sample(old(s)) == (b, s)
    {
      b := CoinExtern.ExternCoinSample();
      assume {:axiom} false;
    }

  }
}

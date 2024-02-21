/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module Coin.Implementation {
  import Model
  import Monad
  import Interface
  import UniformPowerOfTwo

  trait {:termination false} Trait extends Interface.Trait {

    method CoinSample() returns (b: bool)
      modifies `s
      ensures Model.Sample(old(s)) == Monad.Result(b, s)
    {
      var x := UniformPowerOfTwoSample(2);
      b := if x == 1 then true else false;
      reveal UniformPowerOfTwo.Model.Sample();
    }

  }

}

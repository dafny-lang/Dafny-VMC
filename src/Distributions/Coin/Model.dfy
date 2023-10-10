/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module Coin.Model {
  import Partials
  import RandomNumberGenerator
  import Monad

  function Sample(s: RandomNumberGenerator.RNG): Monad.Result<bool> {
    Monad.Deconstruct(s)
  }
}

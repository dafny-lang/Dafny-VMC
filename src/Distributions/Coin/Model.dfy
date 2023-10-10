/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module Coin.Model {
  import Partials
  import RandomNumberGenerator
  import Monad

  function Sample(s: RandomNumberGenerator.RNG): Partials.Partial<(bool, RandomNumberGenerator.RNG)> {
    Monad.Deconstruct(s)
  }
}

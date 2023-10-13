/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module Coin.Model {
  import Random
  import Monad

  function Sample(s: Random.Bitstream): (bool, Random.Bitstream) {
    Monad.Coin(s)
  }
}

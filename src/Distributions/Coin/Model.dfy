/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module Coin.Model {
  import Rand
  import Monad

  function Sample(s: Rand.Bitstream): (bool, Rand.Bitstream) {
    Monad.Coin(s)
  }
}

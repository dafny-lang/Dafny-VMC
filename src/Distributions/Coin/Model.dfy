/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module Coin.Model {
  import Rand
  import Monad`Spec

  function Sample(): Monad.Hurd<bool> {
    Monad.Coin()
  }
}

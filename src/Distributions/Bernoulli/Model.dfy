/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module Bernoulli.Model {
  import Uniform
  import Monad

  // Footnote 5, p. 82
  opaque ghost function Sample(numer: nat, denom: nat): (f: Monad.Hurd<bool>)
    requires denom != 0
    requires numer <= denom
  {
    // TODO: this should use Map instead of Bind
    Monad.Bind(Uniform.Model.Sample(denom), (k: nat) => Monad.Return(k < numer))
  }

}

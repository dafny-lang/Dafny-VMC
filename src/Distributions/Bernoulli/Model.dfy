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
    Monad.Map(Uniform.Model.Sample(denom), (k: nat) => k < numer)
  }

}

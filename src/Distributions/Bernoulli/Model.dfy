/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module Bernoulli.Model {
  import Uniform
  import Monad

  // Footnote 5, p. 82
  ghost function Sample(numer: nat, denom: nat): (f: Monad.Hurd<bool>)
    requires denom != 0
    requires numer <= denom
    ensures forall s :: f(s).Value() == Uniform.Model.Sample(denom)(s).Value().Map(x => x < numer)
    ensures forall s :: f(s).Rng() == Uniform.Model.Sample(denom)(s).Rng()
  {
    Monad.Map((k: nat) => k < numer, Uniform.Model.Sample(denom))
  }

}

/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module Bernoulli.Model {
  import Uniform
  import Monad
  import Partial

  // Footnote 5, p. 82
  ghost function Sample(numer: nat, denom: nat): (f: Partial.Hurd<bool>)
    requires denom != 0
    requires numer <= denom
    ensures forall s :: f(s).0 == Uniform.Model.Sample(denom)(s).0.Map(x => x < numer)
    ensures forall s :: f(s).1 == Uniform.Model.Sample(denom)(s).1
  {
    Partial.Map((k: nat) => k < numer, Uniform.Model.Sample(denom))
  }

}

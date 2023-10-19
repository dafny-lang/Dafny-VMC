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
    ensures forall s :: f(s).0 == (Uniform.Model.Sample(denom)(s).0 < numer)
    ensures forall s :: f(s).1 == Uniform.Model.Sample(denom)(s).1
  {
    Monad.Bind(Uniform.Model.Sample(denom), (k: nat) => Monad.Return(k < numer))
  }

}

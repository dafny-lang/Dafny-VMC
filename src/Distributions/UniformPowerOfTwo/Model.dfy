/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module UniformPowerOfTwo.Model {
  import Helper
  import Rand
  import Quantifier
  import Monad

  // Adapted from Definition 48 (see issue #79 for the reason of the modification)
  // The return value u is uniformly distributed between 0 <= u < 2^k where 2^k <= n < 2^(k + 1).
  opaque function Sample(n: nat): (h: Monad.Hurd<nat>)
    requires n >= 1
    ensures forall s :: Sample(n)(s).Result? // always terminates, not just almost surely
  {
    if n == 1 then
      Monad.Return(0)
    else
      Monad.Bind(Sample(n/2), UnifStep)
  }

  function UnifStepHelper(m: nat): bool -> Monad.Hurd<nat> {
    (b: bool) => Monad.Return(if b then 2*m + 1 else 2*m)
  }

  function UnifStep(m: nat): Monad.Hurd<nat> {
    Monad.Bind(Monad.Coin, UnifStepHelper(m))
  }
}

/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module UniformPowerOfTwo.Model {
  import Helper
  import Rand
  import Quantifier
  import Monad
  import Independence
  import Loops

  function UnifStepHelper(m: nat): (f: bool -> Monad.Hurd<nat>)
    ensures forall b :: Monad.IsAlwaysConverging(f(b))
  {
    (b: bool) => Monad.Return(if b then 2*m + 1 else 2*m)
  }

  function UnifStep(m: nat): (f: Monad.Hurd<nat>)
    ensures Monad.IsAlwaysConverging(f)
  {
    Monad.Bind(Monad.Coin(), UnifStepHelper(m))
  }

  // Adapted from Definition 48 (see issue #79 for the reason of the modification)
  // The return value u is uniformly distributed between 0 <= u < 2^k where 2^k <= n < 2^(k + 1).
  opaque function Sample(n: nat): (h: Monad.Hurd<nat>)
    requires n >= 1
    ensures Monad.IsAlwaysConverging(h) // always terminates, not just almost surely
  {
    if n == 1 then
      Monad.Return(0)
    else
      Monad.Bind(Sample(n/2), UnifStep)
  }

}

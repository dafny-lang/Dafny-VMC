/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module UniformPowerOfTwo.Model {
  import Helper
  import Rand
  import Monad
  import Independence
  import NatArith

  /************
   Definitions
  ************/

  // Adapted from Definition 48 (see issue #79 for the reason of the modification)
  // The return value u is uniformly distributed between 0 <= u < 2^k where 2^k <= n < 2^(k + 1).
  function {:axiom} Sample(n: nat): (h: Monad.Hurd<nat>)
    requires n >= 1
    ensures forall s :: Sample(n)(s).Result? // always terminates, not just almost surely
    ensures n == 2 ==> forall s :: h(s) == Monad.Coin(s).Map(b => if b then 1 else 0)

}
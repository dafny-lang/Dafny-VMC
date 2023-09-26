/*******************************************************************************
*  Copyright by the contributors to the Dafny Project
*  SPDX-License-Identifier: MIT
*******************************************************************************/

include "../../ProbabilisticProgramming/Monad.dfy"
include "../Base/Interface.dfy"

module GeometricInterface {
  import opened BaseInterface
  import opened Monad

  trait {:termination false} IGeometric extends TBase {

    method Geometric() returns (c: nat)
      modifies this
      decreases *
      ensures !old(s)(c)
      ensures forall i | 0 <= i < c :: old(s)(i)
      ensures s == Monad.IterateTail(old(s), c + 1)

  }
}

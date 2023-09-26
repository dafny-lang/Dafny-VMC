/*******************************************************************************
*  Copyright by the contributors to the Dafny Project
*  SPDX-License-Identifier: MIT
*******************************************************************************/

include "../Base/Interface.dfy"
include "Model.dfy"

module UnifInterface {
  import opened BaseInterface
  import opened UnifModel

  trait {:termination false} IUnif extends TBase {

    method Unif(n: nat) returns (u: nat)
      modifies this
      ensures UnifModel.ProbUnif(n)(old(s)) == (u, s)

  }
}

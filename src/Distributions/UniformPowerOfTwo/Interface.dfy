/*******************************************************************************
*  Copyright by the contributors to the Dafny Project
*  SPDX-License-Identifier: MIT
*******************************************************************************/

include "../Base/Interface.dfy"
include "Model.dfy"

module UniformPowerOfTwoInterface {
  import opened BaseInterface
  import opened UniformPowerOfTwoModel

  trait {:termination false} IUniformPowerOfTwo extends TBase {

    method UniformPowerOfTwo(n: nat) returns (u: nat)
      modifies this
      ensures UniformPowerOfTwoModel.ProbUnif(n)(old(s)) == (u, s)

  }
}

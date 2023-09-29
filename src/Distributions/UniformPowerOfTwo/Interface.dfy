/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

include "../Base/Interface.dfy"
include "Model.dfy"

module UniformPowerOfTwoInterface {
  import BaseInterface
  import UniformPowerOfTwoModel

  trait {:termination false} IUniformPowerOfTwo extends BaseInterface.TBase {

    method UniformPowerOfTwo(n: nat) returns (u: nat)
      modifies this
      ensures UniformPowerOfTwoModel.ProbUnif(n)(old(s)) == (u, s)

  }
}

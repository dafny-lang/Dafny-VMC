/*******************************************************************************
*  Copyright by the contributors to the Dafny Project
*  SPDX-License-Identifier: MIT
*******************************************************************************/

include "Interface.dfy"

trait UniformExtern extends IUniform {

  method {:extern} Uniform(n: nat) returns (u: nat)
    modifies this
    decreases *
    requires n > 0
    ensures u < n
    ensures UniformModel.ProbUniform(n)(old(s)) == (u, s)

}

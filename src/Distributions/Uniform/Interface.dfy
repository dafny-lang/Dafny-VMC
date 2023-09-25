/*******************************************************************************
*  Copyright by the contributors to the Dafny Project
*  SPDX-License-Identifier: MIT
*******************************************************************************/

include "../Base/Interface.dfy"
include "Model.dfy"

trait IUniform extends Base, IUnif {

  method Uniform(n: nat) returns (u: nat)
    modifies this
    decreases *
    requires n > 0
    ensures u < n
    ensures UniformModel.ProbUniform(n)(old(s)) == (u, s)

}

trait IUnif extends Base {

  method Unif(n: nat) returns (u: nat)
    modifies this
    ensures UniformModel.ProbUnif(n)(old(s)) == (u, s)

}

/*******************************************************************************
*  Copyright by the contributors to the Dafny Project
*  SPDX-License-Identifier: MIT
*******************************************************************************/

include "../Uniform/Interface.dfy"
include "Model.dfy"

module BernoulliRationalInterface {
  import UniformInterface
  import BernoulliRationalModel
  
  trait {:termination false} IBernoulliRational extends UniformInterface.IUniform {

    method BernoulliRational(m: nat, n: nat) returns (c: bool)
      modifies this
      decreases *
      requires n != 0
      requires m <= n
      ensures BernoulliRationalModel.ProbBernoulliRational(m, n)(old(s)) == (c, s)

  }
}

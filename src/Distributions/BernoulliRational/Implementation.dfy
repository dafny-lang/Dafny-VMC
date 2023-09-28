/*******************************************************************************
*  Copyright by the contributors to the Dafny Project
*  SPDX-License-Identifier: MIT
*******************************************************************************/

include "Interface.dfy"
include "Model.dfy"

module BernoulliRationalImplementation {
  import BernoulliRationalModel
  import BernoulliRationalInterface

  trait {:termination false} TBernoulliRational extends BernoulliRationalInterface.IBernoulliRational {

   method BernoulliRational(m: nat, n: nat) returns (c: bool)
      modifies this
      decreases *
      requires n != 0
      requires m <= n
      ensures BernoulliRationalModel.ProbBernoulliRational(m, n)(old(s)) == (c, s)
    {
      var k := Uniform(n);
      c := k < m;
    }

  }
}

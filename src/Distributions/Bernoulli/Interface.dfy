/*******************************************************************************
*  Copyright by the contributors to the Dafny Project
*  SPDX-License-Identifier: MIT
*******************************************************************************/

include "../Base/Interface.dfy"
include "Model.dfy"

module BernoulliInterface {
  import BernoulliModel
  import BaseInterface

  trait {:termination false} IBernoulli extends BaseInterface.TBase {

    method Bernoulli(p: real) returns (c: bool)
      modifies this
      decreases *
      requires 0.0 <= p <= 1.0
      ensures BernoulliModel.ProbBernoulli(p)(old(s)) == (c, s)

  }
}

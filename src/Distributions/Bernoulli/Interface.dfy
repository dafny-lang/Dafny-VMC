/*******************************************************************************
*  Copyright by the contributors to the Dafny Project
*  SPDX-License-Identifier: MIT
*******************************************************************************/

include "../Base/Interface.dfy"
include "Model.dfy"

import opened BernoulliModel

trait IBernoulli extends Base {

  method Bernoulli(p: real) returns (c: bool)
    modifies this
    decreases *
    requires 0.0 <= p <= 1.0
    ensures BernoulliModel.ProbBernoulli(p)(old(s)) == (c, s)

}

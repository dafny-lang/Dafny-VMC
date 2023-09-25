/*******************************************************************************
*  Copyright by the contributors to the Dafny Project
*  SPDX-License-Identifier: MIT
*******************************************************************************/

include "../Bernoulli/Interface.dfy"
include "../Uniform/Interface.dfy"
include "../BernoulliExpNeg/Interface.dfy"

module IDiscreteLaplace {
  import opened IBernoulli
  import opened IUniform
  import opened IBernoulliExpNeg

  trait {:termination false} IDiscreteLaplace extends IBernoulli, IUniform, IBernoulliExpNeg {

    // Based on Algorithm 2 in https://arxiv.org/pdf/2004.00010.pdf; unverified
    method DiscreteLaplace(s: nat, t: nat) returns (z: int)
      modifies this
      requires s >= 1
      requires t >= 1
      decreases *

  }
}

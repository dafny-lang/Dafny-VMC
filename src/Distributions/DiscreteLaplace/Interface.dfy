/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

include "../../Math/Rationals.dfy"
include "../Bernoulli/Bernoulli.dfy"
include "../Uniform/Interface.dfy"
include "../BernoulliExpNeg/Interface.dfy"

module DiscreteLaplaceInterface {
  import Rationals
  import Bernoulli
  import UniformInterface
  import BernoulliExpNegInterface

  trait {:termination false} IDiscreteLaplace extends Bernoulli.Interface.IBernoulli, UniformInterface.IUniform, BernoulliExpNegInterface.IBernoulliExpNeg {

    // Based on Algorithm 2 in https://arxiv.org/pdf/2004.00010.pdf; unverified
    method DiscreteLaplace(scale: Rationals.Rational) returns (z: int)
      modifies this
      requires scale.numer >= 1
      decreases *

  }
}

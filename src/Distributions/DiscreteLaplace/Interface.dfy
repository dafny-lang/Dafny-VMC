/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

include "../../Math/Rationals.dfy"
include "../Bernoulli/Bernoulli.dfy"
include "../Uniform/Uniform.dfy"
include "../BernoulliExpNeg/BernoulliExpNeg.dfy"

module Interface {
  import Rationals
  import Bernoulli
  import Uniform
  import BernoulliExpNeg

  trait {:termination false} Trait extends Bernoulli.Interface.Trait, Uniform.Interface.Trait, BernoulliExpNeg.Interface.Trait {

    // Based on Algorithm 2 in https://arxiv.org/pdf/2004.00010.pdf; unverified
    method DiscreteLaplaceSample(scale: Rationals.Rational) returns (z: int)
      modifies this
      requires scale.numer >= 1
      decreases *

  }
}

/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module DiscreteLaplace.Interface {
  import Rationals
  import Coin
  import Uniform
  import BernoulliExpNeg

  trait {:termination false} Trait extends Coin.Interface.Trait, Uniform.Interface.Trait, BernoulliExpNeg.Interface.Trait {

    // Based on Algorithm 2 in https://arxiv.org/pdf/2004.00010.pdf; unverified
    method DiscreteLaplaceSample(scale: Rationals.Rational) returns (z: int)
      modifies this
      requires scale.numer >= 1
      decreases *

  }
}

/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module BernoulliExpNeg.Interface {
  import Rationals
  import Partial
  import Bernoulli
  import Model

  trait {:termination false} Trait extends Bernoulli.Interface.Trait {

    method BernoulliExpNegSample(gamma: Rationals.Rational) returns (c: bool)
      modifies this
      decreases *
      requires gamma.numer >= 0
      ensures (Partial.Terminating(c), s) == Model.Sample(gamma)(old(s))

  }
}

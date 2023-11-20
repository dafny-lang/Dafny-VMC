/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module DiscreteGaussian.Implementation {
  import Rationals
  import Interface

  trait {:termination false} Trait extends Interface.Trait {

    // Based on Algorithm 3 in https://arxiv.org/pdf/2004.00010.pdf; unverified
    // Note that we take sigma as a parameter, not sigma^2, to avoid square roots.
    method DiscreteGaussianSample(sigma: Rationals.Rational) returns (y: int)
      modifies this
      requires sigma.numer >= 1
      decreases *
    {
      var sigmaSquared := sigma.Mul(sigma);
      var t := sigma.Floor() + 1;
      while true
        decreases *
      {
        y := DiscreteLaplaceSample(Rationals.Int(t));
        var yAbs := if y < 0 then -y else y;
        var numeratorTerm := Rationals.Int(yAbs).Sub(sigmaSquared.Div(Rationals.Int(t)));
        var gamma := numeratorTerm.Mul(numeratorTerm)
        .Div(Rationals.Int(2).Mul(sigmaSquared));
        var c := BernoulliExpNegSample(gamma);
        if c {
          return;
        }
      }
    }

  }
}

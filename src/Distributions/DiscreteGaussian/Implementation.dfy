/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

include "../../Math/Rationals.dfy"
include "Interface.dfy"

module DiscreteGaussianImplementation {
  import Rationals
  import DiscreteGaussianInterface

  trait {:termination false} TDiscreteGaussian extends DiscreteGaussianInterface.IDiscreteGaussian {

    // Based on Algorithm 3 in https://arxiv.org/pdf/2004.00010.pdf; unverified
    // Note that we take sigma as a parameter, not sigma^2, to avoid square roots.
    method DiscreteGaussian(sigma: Rationals.Rational) returns (y: int)
      modifies this
      requires sigma.numer >= 1
      decreases *
    {
      var sigmaSquared := Rationals.Mul(sigma, sigma);
      var t := Rationals.Floor(sigma) + 1;
      while true
        decreases *
      {
        y := DiscreteLaplace(Rationals.Int(t));
        var yAbs := if y < 0 then -y else y;
        var numeratorTerm := Rationals.Sub(
          Rationals.Int(yAbs),
          Rationals.Div(sigmaSquared, Rationals.Int(t))
        );
        var gamma := Rationals.Div(
          Rationals.Mul(numeratorTerm, numeratorTerm),
          Rationals.Mul(
            Rationals.Int(2),
            sigmaSquared
          )
        );
        var c := BernoulliExpNeg(gamma);
        if c {
          return;
        }
      }
    }

  }
}

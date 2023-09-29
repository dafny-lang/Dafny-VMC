/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

include "Interface.dfy"

module DiscreteGaussianImplementation {
  import DiscreteGaussianInterface

  trait {:termination false} TDiscreteGaussian extends DiscreteGaussianInterface.IDiscreteGaussian {

    // Based on Algorithm 3 in https://arxiv.org/pdf/2004.00010.pdf; unverified
    // Note that we take sigma as a parameter, not sigma^2, to avoid square roots.
    method DiscreteGaussian(sigma: real) returns (y: int)
      modifies this
      requires sigma > 0.0
      decreases *
    {
      var t := sigma.Floor + 1;
      while true
        decreases *
      {
        y := DiscreteLaplace(1, t);
        var y_abs := if y < 0 then -y else y;
        var numerator_term := y_abs as real - sigma * sigma / t as real;
        var c := BernoulliExpNeg(numerator_term * numerator_term / 2.0 / sigma / sigma);
        if c {
          return;
        }
      }
    }

  }
}

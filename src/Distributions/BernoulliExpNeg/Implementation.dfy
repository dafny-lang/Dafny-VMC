/*******************************************************************************
*  Copyright by the contributors to the Dafny Project
*  SPDX-License-Identifier: MIT
*******************************************************************************/

include "../Bernoulli/Interface.dfy"
include "Interface.dfy"

module BernoulliExpNegImplementation {
  import BernoulliExpNegInterface

  trait {:termination false} TBernoulliExpNeg extends BernoulliExpNegInterface.IBernoulliExpNeg {

    // Based on Algorithm 1 in https://arxiv.org/pdf/2004.00010.pdf; unverified
    method BernoulliExpNeg(gamma: real) returns (c: bool)
      modifies this
      decreases *
      requires gamma >= 0.0
    {
      if gamma <= 1.0 {
        var k := 1;
        var a := Bernoulli(gamma / (k as real));
        while a
          decreases *
        {
          k := k + 1;
          a := Bernoulli(gamma / (k as real));
        }
        c := k % 2 == 1;
      } else {
        var k := 1;
        while k <= gamma.Floor {
          var b := BernoulliExpNeg(1.0);
          if !b {
            return false;
          }
          k := k + 1;
        }
        c:= BernoulliExpNeg(gamma - gamma.Floor as real);
      }
    }

  }
}

/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

include "../../Math/Rationals.dfy"
include "../BernoulliRational/Interface.dfy"
include "Interface.dfy"

module BernoulliExpNegImplementation {
  import Rationals
  import BernoulliExpNegInterface

  trait {:termination false} TBernoulliExpNeg extends BernoulliExpNegInterface.IBernoulliExpNeg {

    // Based on Algorithm 1 in https://arxiv.org/pdf/2004.00010.pdf; unverified
    method BernoulliExpNeg(gamma: Rationals.Rational) returns (c: bool)
      modifies this
      requires gamma.numer >= 0
      decreases *
    {
      if gamma.numer <= gamma.denom {
        var k := 1;
        var a := BernoulliRational(Rationals.Rational(gamma.numer, k * gamma.denom));
        while a
          decreases *
        {
          k := k + 1;
          a := BernoulliRational(Rationals.Rational(gamma.numer, k * gamma.denom));
        }
        c := k % 2 == 1;
      } else {
        var k := 1;
        while k <= Rationals.Floor(gamma) {
          var b := BernoulliExpNeg(Rationals.Int(1));
          if !b {
            return false;
          }
          k := k + 1;
        }
        c:= BernoulliExpNeg(Rationals.Fractional(gamma));
      }
    }

  }
}

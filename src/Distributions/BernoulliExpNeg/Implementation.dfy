/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module BernoulliExpNeg.Implementation {
  import Rationals
  import Interface

  trait {:termination false} Trait extends Interface.Trait {

    // Based on Algorithm 1 in https://arxiv.org/pdf/2004.00010.pdf; unverified
    method BernoulliExpNegSample(gamma: Rationals.Rational) returns (c: bool)
      modifies this
      requires gamma.numer >= 0
      decreases *
    {
      if gamma.numer <= gamma.denom {
        var k := 1;
        var a := BernoulliSample(Rationals.Rational(gamma.numer, k * gamma.denom));
        while a
          decreases *
        {
          k := k + 1;
          a := BernoulliSample(Rationals.Rational(gamma.numer, k * gamma.denom));
        }
        c := k % 2 == 1;
      } else {
        var k := 1;
        while k <= Rationals.Floor(gamma) {
          var b := BernoulliExpNegSample(Rationals.Int(1));
          if !b {
            return false;
          }
          k := k + 1;
        }
        c:= BernoulliExpNegSample(Rationals.FractionalPart(gamma));
      }
    }

  }
}

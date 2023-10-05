/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

include "../../Math/Rationals.dfy"
include "Interface.dfy"

module DiscreteLaplace.Implementation {
  import Rationals
  import Interface

  trait {:termination false} Trait extends Interface.Trait {

    // Based on Algorithm 2 in https://arxiv.org/pdf/2004.00010.pdf; unverified
    method DiscreteLaplaceSample(scale: Rationals.Rational) returns (z: int)
      modifies this
      requires scale.numer >= 1
      decreases *
    {
      var b := true;
      var y := 0;
      while b && y == 0
        decreases *
      {
        var u := UniformSample(scale.numer);
        var d := BernoulliExpNegSample(Rationals.Rational(u, scale.numer));
        if !d {
          continue;
        }
        var v := 0;
        var a := true;
        while a
          decreases *
        {
          a := BernoulliExpNegSample(Rationals.Int(1));
          if a {
            v := v + 1;
          }
        }
        var x := u + scale.numer * v;
        y := x / scale.denom;
        b := BernoulliSample(Rationals.Rational(1, 2));
      }
      z := if b then -y else y;
    }

  }
}

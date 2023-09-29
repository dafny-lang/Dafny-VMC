/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

include "../../Math/Rationals.dfy"
include "Interface.dfy"

module DiscreteLaplaceImplementation {
  import Rationals
  import DiscreteLaplaceInterface

  trait {:termination false} TDiscreteLaplace extends DiscreteLaplaceInterface.IDiscreteLaplace {

    // Based on Algorithm 2 in https://arxiv.org/pdf/2004.00010.pdf; unverified
    method DiscreteLaplace(scale: Rationals.Rational) returns (z: int)
      modifies this
      requires scale.numer >= 1
      decreases *
    {
      var b := true;
      var y := 0;
      while b && y == 0
        decreases *
      {
        var u := Uniform(scale.numer);
        var d := BernoulliExpNeg(Rationals.Rational(u, scale.numer));
        if !d {
          continue;
        }
        var v := 0;
        var a := true;
        while a
          decreases *
        {
          a := BernoulliExpNeg(Rationals.Int(1));
          if a {
            v := v + 1;
          }
        }
        var x := u + scale.numer * v;
        y := x / scale.denom;
        b := Bernoulli(0.5);
      }
      z := if b then -y else y;
    }

  }
}

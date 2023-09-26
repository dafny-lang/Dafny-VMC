/*******************************************************************************
*  Copyright by the contributors to the Dafny Project
*  SPDX-License-Identifier: MIT
*******************************************************************************/

include "Interface.dfy"

module DiscreteLaplaceImplementation {
  import opened DiscreteLaplaceInterface

  trait {:termination false} TDiscreteLaplace extends IDiscreteLaplace {

    // Based on Algorithm 2 in https://arxiv.org/pdf/2004.00010.pdf; unverified
    method DiscreteLaplace(s: nat, t: nat) returns (z: int)
      modifies this
      requires s >= 1
      requires t >= 1
      decreases *
    {
      var b := true;
      var y := 0;
      while b && y == 0
        decreases *
      {
        var u := Uniform(t);
        var d := BernoulliExpNeg(u as real / t as real);
        if !d {
          continue;
        }
        var v := 0;
        var a := true;
        while a
          decreases *
        {
          a := BernoulliExpNeg(1.0);
          if a {
            v := v + 1;
          }
        }
        var x := u + t * v;
        y := x / s;
        b := Bernoulli(0.5);
      }
      z := if b then -y else y;
    }

  }
}

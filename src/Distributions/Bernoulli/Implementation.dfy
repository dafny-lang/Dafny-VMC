/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

include "../../Math/MeasureTheory.dfy"
include "Interface.dfy"
include "Model.dfy"

module BernoulliImplementation {
  import MeasureTheory
  import BernoulliModel
  import BernoulliInterface

  trait {:termination false} TBernoulli extends BernoulliInterface.IBernoulli {

    method Bernoulli(p: real) returns (c: bool)
      modifies this
      decreases *
      requires 0.0 <= p <= 1.0
      ensures BernoulliModel.ProbBernoulli(p)(old(s)) == (c, s)
    {
      var q: MeasureTheory.Probability := p as real;

      var b := Coin();
      if b {
        if q <= 0.5 {
          return false;
        } else {
          q := 2.0 * (q as real) - 1.0;
        }
      } else {
        if q <= 0.5 {
          q := 2.0 * (q as real);
        } else {
          return true;
        }
      }

      while true
        invariant BernoulliModel.ProbBernoulli(p)(old(s)) == BernoulliModel.ProbBernoulli(q)(s)
        decreases *
      {
        b := Coin();
        if b {
          if q <= 0.5 {
            return false;
          } else {
            q := 2.0 * (q as real) - 1.0;
          }
        } else {
          if q <= 0.5 {
            q := 2.0 * (q as real);
          } else {
            return true;
          }
        }
      }
    }

  }
}

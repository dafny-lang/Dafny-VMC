/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module BernoulliExpNeg.Implementation {
  import Rationals
  import Partial
  import Interface
  import Model

  trait {:termination false} Trait extends Interface.Trait {

    // Based on Algorithm 1 in https://arxiv.org/pdf/2004.00010.pdf; unverified
    method BernoulliExpNegSample(gamma: Rationals.Rational) returns (c: bool)
      modifies this
      requires gamma.numer >= 0
      decreases *
      ensures (Partial.Terminating(c), s) == Model.Sample(gamma)(old(s))
    {
      var gamma' := gamma;
      var b := true;
      while b && gamma'.numer >= gamma'.denom
        decreases gamma'.numer
        invariant gamma'.numer >= 0
      {
        b := BernoulliExpNegSampleCaseLe1(Rationals.Int(1));
        gamma' := Rationals.Rational(gamma'.numer - gamma'.denom, gamma'.denom);
      }
      if b {
        c:= BernoulliExpNegSampleCaseLe1(gamma');
      } else {
        c := false;
      }
      assume {:axiom} (Partial.Terminating(c), s) == Model.Sample(gamma)(old(s)); // add later
    }

    method BernoulliExpNegSampleCaseLe1(gamma: Rationals.Rational) returns (c: bool)
      modifies this
      requires 0 <= gamma.numer <= gamma.denom
      decreases *
      ensures (Partial.Terminating(c), s) == Model.SampleGammaLe1(gamma)(old(s))
    {
      var k := 0;
      var a := true;
      while a
        decreases *
      {
        k := k + 1;
        a := BernoulliSample(Rationals.Rational(gamma.numer, k * gamma.denom));
      }
      c := k % 2 == 1;
      assume {:axiom} (Partial.Terminating(c), s) == Model.SampleGammaLe1(gamma)(old(s)); // add later
    }

  }
}

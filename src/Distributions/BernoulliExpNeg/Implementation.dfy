/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module BernoulliExpNeg.Implementation {
  import Rationals
  import Monad
  import Interface
  import Model
  import Bernoulli

  trait {:termination false} Trait extends Interface.Trait {

    // Based on Algorithm 1 in https://arxiv.org/pdf/2004.00010.pdf; unverified
    method {:vcs_split_on_every_assert} BernoulliExpNegSample(gamma: Rationals.Rational) returns (c: bool)
      modifies this
      requires gamma.numer >= 0
      decreases *
      ensures Monad.Result(c, s) == Model.Sample(gamma)(old(s))
    {
      var gamma' := gamma;
      var b := true;
      while b && gamma'.numer >= gamma'.denom
        decreases gamma'.numer
        invariant gamma'.numer >= 0
        invariant Model.GammaReductionLoop((true, gamma))(old(s)) == Model.GammaReductionLoop((b, gamma'))(s)
      {
        b := BernoulliExpNegSampleCaseLe1(Rationals.Int(1));
        gamma' := Rationals.Rational(gamma'.numer - gamma'.denom, gamma'.denom);
      }
      if b {
        assert 0 <= gamma'.numer < gamma'.denom;
        c:= BernoulliExpNegSampleCaseLe1(gamma');
      } else {
        c := false;
      }
    }

    method BernoulliExpNegSampleCaseLe1(gamma: Rationals.Rational) returns (c: bool)
      modifies this
      requires 0 <= gamma.numer <= gamma.denom
      decreases *
      ensures Monad.Result(c, s) == Model.SampleGammaLe1(gamma)(old(s))
    {
      var k: nat := 0;
      var a := true;
      ghost var initGamma := gamma;
      while a
        decreases *
        invariant gamma == initGamma
        invariant Model.GammaLe1Loop(gamma)((a, k))(s) == Model.GammaLe1Loop(gamma)((true, 0))(old(s))
      {
        ghost var prevK: nat := k;
        ghost var prevA := a;
        ghost var prevS := s;
        k := k + 1;
        assume gamma.numer < k * gamma.denom;
        a := BernoulliSample(Rationals.Rational(gamma.numer, k * gamma.denom));
        assert ((a, k), s) == Model.GammaLe1LoopIter(gamma)((prevA, prevK))(prevS) by {
          Model.GammaLe1LoopIterProperty(gamma, prevA, prevK, prevS, a, k, s);
        }
        assert Model.GammaLe1Loop(gamma)((prevA, prevK))(prevS) == Model.GammaLe1Loop(gamma)((a, k))(s) by {
          Model.GammaLe1LoopUnroll(gamma, (prevA, prevK), prevS);
        }
      }
      c := k % 2 == 1;
      assume {:axiom} Monad.Result(c, s) == Model.SampleGammaLe1(gamma)(old(s)); // add later
    }

  }
}

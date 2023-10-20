/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module BernoulliExpNeg.Implementation {
  import Helper
  import Rationals
  import Rand
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
      assert GammaLe1LoopInvariant(gamma, old(s), a, k, s) by {
        reveal GammaLe1LoopInvariant();
      }
      while a
        decreases *
        invariant 0 <= gamma.numer <= gamma.denom
        invariant GammaLe1LoopInvariant(gamma, old(s), a, k, s)
      {
        ghost var prevK: nat := k;
        ghost var prevA := a;
        ghost var prevS := s;
        k := k + 1;
        Helper.MulMonotonic(1, gamma.denom, k, gamma.denom);
        a := BernoulliSample(Rationals.Rational(gamma.numer, k * gamma.denom));
        Model.GammaLe1LoopIterProperty(gamma, prevA, prevK, prevS, a, k, s);
        EnsureLoopInvariant(gamma, old(s), prevK, prevS, a, k, s);
      }
      c := k % 2 == 1;
      EnsurePostCondition(gamma, old(s), k, s, c);
    }

    opaque ghost predicate GammaLe1LoopInvariant(gamma: Rationals.Rational, oldS: Rand.Bitstream, a: bool, k: nat, s: Rand.Bitstream)
      requires 0 <= gamma.numer <= gamma.denom
    {
      Model.GammaLe1Loop(gamma)((true, 0))(oldS) == Model.GammaLe1Loop(gamma)((a, k))(s)
    }

    lemma EnsureLoopInvariant(gamma: Rationals.Rational, oldS: Rand.Bitstream, k: nat, s: Rand.Bitstream, a': bool, k': nat, s': Rand.Bitstream)
      requires 0 <= gamma.numer <= gamma.denom
      requires inv: GammaLe1LoopInvariant(gamma, oldS, true, k, s)
      requires iter: Monad.Result((a', k'), s') == Model.GammaLe1LoopIter(gamma)((true, k))(s)
      ensures GammaLe1LoopInvariant(gamma, oldS, a', k', s')
    {
      calc {
        Model.GammaLe1Loop(gamma)((true, 0))(oldS);
        { reveal GammaLe1LoopInvariant(); reveal inv; }
        Model.GammaLe1Loop(gamma)((true, k))(s);
        { reveal iter; Model.GammaLe1LoopUnroll(gamma, (true, k), s); }
        Model.GammaLe1Loop(gamma)((a', k'))(s');
      }
      reveal GammaLe1LoopInvariant();
    }

    lemma EnsurePostCondition(gamma: Rationals.Rational, oldS: Rand.Bitstream, k: nat, s: Rand.Bitstream, c: bool)
      requires 0 <= gamma.numer <= gamma.denom
      requires GammaLe1LoopInvariant(gamma, oldS, false, k, s)
      requires c <==> (k % 2 == 1)
      ensures Monad.Result(c, s) == Model.SampleGammaLe1(gamma)(oldS)
    {
      calc {
        Model.GammaLe1Loop(gamma)((true, 0))(oldS);
        { reveal GammaLe1LoopInvariant(); }
        Model.GammaLe1Loop(gamma)((false, k))(s);
        { reveal Model.GammaLe1Loop(); }
        Monad.Result((false, k), s);
      }
    }
  }
}

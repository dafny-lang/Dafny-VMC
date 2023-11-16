/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module BernoulliExpNeg.Equivalence {
  import Rationals
  import Rand
  import Monad
  import Model
  import Loops
  import Bernoulli

  /************
   Definitions
  ************/

  opaque ghost predicate CaseLe1LoopInvariant(gamma: Rationals.Rational, oldS: Rand.Bitstream, a: bool, k: nat, s: Rand.Bitstream)
    requires 0 <= gamma.numer <= gamma.denom
  {
    Model.GammaLe1Loop(gamma)((true, 0))(oldS) == Model.GammaLe1Loop(gamma)((a, k))(s)
  }

  /*******
   Lemmas
  *******/

  lemma SampleUnfold(gamma: Rationals.Rational, s: Rand.Bitstream, prevGamma: Rationals.Rational, prevS: Rand.Bitstream, b: bool)
    requires gamma.numer > 0
    requires prevGamma.denom == gamma.denom
    requires prevGamma.numer == gamma.numer + gamma.denom
    requires Model.SampleGammaLe1(Rationals.Int(1))(prevS) == Monad.Result(b, s)
    ensures Model.Sample(prevGamma)(prevS) == if b then Model.Sample(gamma)(s) else Monad.Result(false, s)
  {
    reveal Model.Sample();
  }

  lemma GammaLe1LoopUnroll(gamma: Rationals.Rational, ak: (bool, nat), s: Rand.Bitstream)
    requires 0 <= gamma.numer <= gamma.denom
    requires ak.0
    ensures Model.GammaLe1Loop(gamma)(ak)(s) == Monad.Bind(Model.GammaLe1LoopIter(gamma)(ak), Model.GammaLe1Loop(gamma))(s)
  {
    Model.GammaLe1LoopTerminatesAlmostSurely(gamma);
    calc {
      Model.GammaLe1Loop(gamma)(ak)(s);
      { reveal Model.GammaLe1Loop(); }
      Loops.While(Model.GammaLe1LoopCondition, Model.GammaLe1LoopIter(gamma))(ak)(s);
      { reveal Model.GammaLe1Loop();
        Loops.WhileUnroll(Model.GammaLe1LoopCondition, Model.GammaLe1LoopIter(gamma), ak, s); }
      Monad.Bind(Model.GammaLe1LoopIter(gamma)(ak), Model.GammaLe1Loop(gamma))(s);
    }
  }

  lemma EnsureCaseLe1LoopInvariantOnEntry(gamma: Rationals.Rational, s: Rand.Bitstream)
    requires 0 <= gamma.numer <= gamma.denom
    ensures CaseLe1LoopInvariant(gamma, s, true, 0, s)
  {
    reveal CaseLe1LoopInvariant();
  }

  lemma EnsureCaseLe1LoopInvariantMaintained(gamma: Rationals.Rational, oldS: Rand.Bitstream, k: nat, s: Rand.Bitstream, a': bool, k': nat, s': Rand.Bitstream)
    requires 0 <= gamma.numer <= gamma.denom
    requires k' == k + 1
    requires inv: CaseLe1LoopInvariant(gamma, oldS, true, k, s)
    requires bernoulli: Monad.Result(a' , s') == Bernoulli.Model.Sample(gamma.numer, k' * gamma.denom)(s)
    ensures CaseLe1LoopInvariant(gamma, oldS, a', k', s')
  {
    assert iter: Monad.Result((a', k'), s') == Model.GammaLe1LoopIter(gamma)((true, k))(s) by {
      reveal bernoulli;
    }
    calc {
      Model.GammaLe1Loop(gamma)((true, 0))(oldS);
      { reveal CaseLe1LoopInvariant(); reveal inv; }
      Model.GammaLe1Loop(gamma)((true, k))(s);
      { reveal iter; GammaLe1LoopUnroll(gamma, (true, k), s); }
      Model.GammaLe1Loop(gamma)((a', k'))(s');
    }
    reveal CaseLe1LoopInvariant();
  }

  lemma EnsureCaseLe1PostCondition(gamma: Rationals.Rational, oldS: Rand.Bitstream, k: nat, s: Rand.Bitstream, c: bool)
    requires 0 <= gamma.numer <= gamma.denom
    requires CaseLe1LoopInvariant(gamma, oldS, false, k, s)
    requires c <==> (k % 2 == 1)
    ensures Monad.Result(c, s) == Model.SampleGammaLe1(gamma)(oldS)
  {
    calc {
      Model.GammaLe1Loop(gamma)((true, 0))(oldS);
      { reveal CaseLe1LoopInvariant(); }
      Model.GammaLe1Loop(gamma)((false, k))(s);
      { reveal Model.GammaLe1Loop(); }
      Monad.Result((false, k), s);
    }
  }
}

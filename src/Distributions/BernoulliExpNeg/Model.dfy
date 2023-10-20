/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module BernoulliExpNeg.Model {
  import Rationals
  import Rand
  import Uniform
  import Bernoulli
  import Monad
  import Loops
  import BernoulliModel = Bernoulli.Model

  ghost function Sample(gamma: Rationals.Rational): Monad.Hurd<bool>
    requires gamma.denom != 0
    requires gamma.numer >= 0
  {
    Monad.Bind(
      GammaReductionLoop((true, gamma)),
      (bgamma: (bool, Rationals.Rational)) =>
        var res: Monad.Hurd<bool> :=
          if bgamma.0 then
            // This if condition should not be needed, but Monad.Bind does not accept functions with preconditions
            if 0 <= bgamma.1.numer <= bgamma.1.denom
            then SampleGammaLe1(bgamma.1)
            else Monad.Return(false) // return a dummy value because this path should never be taken
          else
            Monad.Return(false);
        res
    )
  }

  ghost function GammaReductionLoop(bgamma: (bool, Rationals.Rational)): Monad.Hurd<(bool, Rationals.Rational)>
    requires bgamma.1.numer >= 0
    decreases bgamma.1.numer
  {
    if !bgamma.0 || bgamma.1.numer < bgamma.1.denom
    then Monad.Return(bgamma)
    else Monad.Bind(
      GammaReductionLoopIter(bgamma),
      (bgamma': (bool, Rationals.Rational)) =>
        var res: Monad.Hurd<(bool, Rationals.Rational)> :=
          // This if condition should not be needed, but Monad.Bind does not accept functions with preconditions
          if bgamma'.1.numer < 0 || bgamma'.1.numer >= bgamma.1.numer
          then Monad.Return((bgamma'.0, Rationals.Rational(0, 1)))
          else GammaReductionLoop(bgamma'); // return a dummy value because this path should never be taken
        res
    )
  }

  ghost function GammaReductionLoopIter(bgamma: (bool, Rationals.Rational)): Monad.Hurd<(bool, Rationals.Rational)>
    requires bgamma.1.numer >= 0
  {
    Monad.Bind(
      SampleGammaLe1(Rationals.Int(1)),
      b' => Monad.Return((b', Rationals.Rational(bgamma.1.numer - bgamma.1.denom, bgamma.1.denom)))
    )
  }

  ghost function SampleGammaLe1(gamma: Rationals.Rational): Monad.Hurd<bool>
  requires 0 <= gamma.numer <= gamma.denom
  {
    Monad.Bind(
      GammaLe1Loop(gamma)((true, 0)),
      (ak: (bool, nat)) => Monad.Return(ak.1 % 2 == 1)
    )
  }

  opaque ghost function GammaLe1Loop(gamma: Rationals.Rational): ((bool, nat)) -> Monad.Hurd<(bool, nat)>
    requires 0 <= gamma.numer <= gamma.denom
  {
    (ak: (bool, nat)) =>
      GammaLe1LoopTerminatesAlmostSurely(gamma);
      Loops.While(
        GammaLe1LoopCondition,
        GammaLe1LoopIter(gamma),
        ak
      )
  }

  ghost function GammaLe1LoopCondition(ak: (bool, nat)): bool {
    ak.0
  }

  ghost function GammaLe1LoopIter(gamma: Rationals.Rational): ((bool, nat)) -> Monad.Hurd<(bool, nat)>
    requires 0 <= gamma.numer <= gamma.denom
  {
    (ak: (bool, nat)) =>
      var res: Monad.Hurd<(bool, nat)> := Monad.Bind(
        BernoulliModel.Sample(gamma.numer, (ak.1 + 1) * gamma.denom),
        (a': bool) => Monad.Return((a', ak.1 + 1)));
      res
  }

  lemma SampleGammaLe1Property(gamma: Rationals.Rational, k: nat, s: Rand.Bitstream)
    requires 0 <= gamma.numer <= gamma.denom
    requires Monad.Result((false, k), s) == GammaLe1Loop(gamma)((true, 0))(s)
    ensures Monad.Result(k % 2 == 1, s) == SampleGammaLe1(gamma)(s)
  {}

  lemma {:vcs_split_on_every_assert} GammaLe1LoopIterProperty(gamma: Rationals.Rational, a: bool, k: nat, s: Rand.Bitstream, a': bool, k': nat, s': Rand.Bitstream)
    requires 0 <= gamma.numer <= gamma.denom
    requires k' == k + 1
    requires Monad.Result(a' , s') == Bernoulli.Model.Sample(gamma.numer, k' * gamma.denom)(s)
    ensures Monad.Result((a', k'), s') == GammaLe1LoopIter(gamma)((a,k))(s)
  {
    var Result(a, s') := Bernoulli.Model.Sample(gamma.numer, k' * gamma.denom)(s);
    assert GammaLe1LoopIter(gamma)((a, k))(s) == Monad.Result((a', k'), s');
    assert Monad.Bind(Bernoulli.Model.Sample(gamma.numer, k' * gamma.denom), a => Monad.Return((a, k')))(s) == Monad.Result((a, k'), s');
  }

  lemma {:axiom} GammaLe1LoopTerminatesAlmostSurely(gamma: Rationals.Rational)
    requires 0 <= gamma.numer <= gamma.denom
    ensures Loops.WhileTerminatesAlmostSurely(GammaLe1LoopCondition, GammaLe1LoopIter(gamma))

  lemma GammaLe1LoopUnroll(gamma: Rationals.Rational, ak: (bool, nat), s: Rand.Bitstream)
    requires 0 <= gamma.numer <= gamma.denom
    requires ak.0
    ensures GammaLe1Loop(gamma)(ak)(s) == Monad.Bind(GammaLe1LoopIter(gamma)(ak), GammaLe1Loop(gamma))(s)
  {
    GammaLe1LoopTerminatesAlmostSurely(gamma);
    assert Eq: forall ak': (bool, nat), s: Rand.Bitstream ::
      GammaLe1Loop(gamma)(ak')(s) == Loops.While(GammaLe1LoopCondition, GammaLe1LoopIter(gamma), ak')(s) by {
        forall ak': (bool, nat), s: Rand.Bitstream ensures GammaLe1Loop(gamma)(ak')(s) == Loops.While(GammaLe1LoopCondition, GammaLe1LoopIter(gamma), ak')(s) {}
      }
    calc {
      GammaLe1Loop(gamma)(ak)(s);
      Loops.While(GammaLe1LoopCondition, GammaLe1LoopIter(gamma), ak)(s);
      { Loops.WhileUnroll(GammaLe1LoopCondition, GammaLe1LoopIter(gamma), ak, s); }
      Monad.Bind(
        GammaLe1LoopIter(gamma)(ak),
        (ak': (bool, nat)) => Loops.While(GammaLe1LoopCondition, GammaLe1LoopIter(gamma), ak'))
      (s);
      { reveal Eq; }
      Monad.Bind(GammaLe1LoopIter(gamma)(ak), GammaLe1Loop(gamma))(s);
    }
  }
}

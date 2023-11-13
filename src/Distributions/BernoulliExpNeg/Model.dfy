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

  opaque ghost function Sample(gamma: Rationals.Rational): Monad.Hurd<bool>
    requires gamma.denom != 0
    requires gamma.numer >= 0
  {
    Monad.Bind(
      GammaReductionLoop((true, gamma)),
      (bgamma: (bool, Rationals.Rational)) =>
        var res: Monad.Hurd<bool> :=
          if bgamma.0 then
            // The else path should never be taken, but we cannot turn this into a precondition
            // because Monad.Bind does not accept functions with preconditions.
            // We return a dummy value in the else-branch.
            if 0 <= bgamma.1.numer <= bgamma.1.denom
            then SampleGammaLe1(bgamma.1)
            else Monad.Return(false) // dummy value
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
            // The else path should never be taken, but we cannot turn this into a precondition
            // because Monad.Bind does not accept functions with preconditions.
            // We return a dummy value in the else-branch.
            if 0 <= bgamma'.1.numer < bgamma.1.numer
            then GammaReductionLoop(bgamma')
            else Monad.Return((bgamma'.0, Rationals.Rational(0, 1))); // dummy value
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
    GammaLe1LoopTerminatesAlmostSurely(gamma);
    Monad.While(
      GammaLe1LoopCondition,
      GammaLe1LoopIter(gamma)
    )
  }

  ghost function GammaLe1LoopCondition(ak: (bool, nat)): bool {
    ak.0
  }

  ghost function GammaLe1LoopIter(gamma: Rationals.Rational): ((bool, nat)) -> Monad.Hurd<(bool, nat)>
    requires 0 <= gamma.numer <= gamma.denom
  {
    (ak: (bool, nat)) =>
      var k' := ak.1 + 1;
      Monad.Bind(
        BernoulliModel.Sample(gamma.numer, k' * gamma.denom),
        SetK(k'))
  }

  ghost function SetK(k: nat): bool -> Monad.Hurd<(bool, nat)> {
    a => Monad.Return((a, k))
  }

  lemma {:axiom} GammaLe1LoopTerminatesAlmostSurely(gamma: Rationals.Rational)
    requires 0 <= gamma.numer <= gamma.denom
    ensures Monad.WhileTerminatesAlmostSurely(GammaLe1LoopCondition, GammaLe1LoopIter(gamma))


}

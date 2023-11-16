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
    decreases gamma.numer
  {
    if gamma.numer <= gamma.denom
    then SampleGammaLe1(gamma)
    else Monad.Bind(
        SampleGammaLe1(Rationals.Int(1)),
        b =>
          var res: Monad.Hurd<bool> :=
            if b
            then Sample(Rationals.Rational(gamma.numer - gamma.denom, gamma.denom))
            else Monad.Return(false);
          res
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
    Loops.While(
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
    ensures Loops.WhileTerminatesAlmostSurely(GammaLe1LoopCondition, GammaLe1LoopIter(gamma))


}

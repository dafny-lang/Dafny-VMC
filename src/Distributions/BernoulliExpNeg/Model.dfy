/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module BernoulliExpNeg.Model {
  import Rationals
  import Uniform
  import Monad
  import Loops
  import BernoulliModel = Bernoulli.Model

  ghost function Sample(gamma: Rationals.Rational): Monad.Hurd<bool>
    requires gamma.denom != 0
    requires gamma.numer >= 0
  {
    Monad.Bind(
      GammaReductionLoop(gamma),
      (bgamma: (bool, Rationals.Rational)) =>
        if bgamma.0 then
          SampleGammaLe1(bgamma.1)
        else
          Monad.Return(false)
    )
  }

  ghost function GammaReductionLoop(gamma: Rationals.Rational): Monad.Hurd<(bool, Rationals.Rational)>
    requires gamma.numer >= 0
  {
    assume {:axiom} false; // assume termination
    Loops.While(
      (bgamma: (bool, Rationals.Rational)) => bgamma.0 && bgamma.1.denom <= bgamma.1.numer,
      GammaReductionLoopIter,
      (true, gamma)
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
  {
    if 0 <= gamma.numer <= gamma.denom
    then Monad.Bind(
           GammaLe1Loop(gamma, (true, 0)),
           (ak: (bool, nat)) => Monad.Return(ak.1 % 2 == 1)
         )
    else Monad.Return(false) // to keep this function total, we return a dummy value here
  }

  ghost function GammaLe1Loop(gamma: Rationals.Rational, ak: (bool, nat)): Monad.Hurd<(bool, nat)>
    requires 0 <= gamma.numer <= gamma.denom
  {
    assume {:axiom} false; // assume termination
    Loops.While(
      (ak: (bool, nat)) => ak.0,
      (ak: (bool, nat)) => GammaLe1LoopIter(gamma, ak),
      ak
    )
  }

  ghost function GammaLe1LoopIter(gamma: Rationals.Rational, ak: (bool, nat)): Monad.Hurd<(bool, nat)>
    requires 0 <= gamma.numer <= gamma.denom
  {
    Monad.Bind(
      BernoulliModel.Sample(gamma.numer, (ak.1 + 1) * gamma.denom),
      (a': bool) => Monad.Return((a', ak.1 + 1))
    )
  }
}

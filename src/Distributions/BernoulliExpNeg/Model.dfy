/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module BernoulliExpNeg.Model {
  import Rationals
  import Uniform
  import Monad
  import Partial
  import WhileAndUntil
  import BernoulliModel = Bernoulli.Model

  ghost function Sample(gamma: Rationals.Rational): Partial.Hurd<bool>
    requires gamma.denom != 0
    requires gamma.numer >= 0
  {
    Partial.Bind(
      GammaReductionLoop(true, gamma),
      (bgamma: (bool, Rationals.Rational)) =>
        if bgamma.0 then
          SampleGammaLe1(bgamma.1)
        else
          Partial.Return(false)
    )
  }

  ghost function GammaReductionLoop(b: bool, gamma: Rationals.Rational): Partial.Hurd<(bool, Rationals.Rational)>
    requires gamma.numer >= 0
    decreases gamma.numer
  {
    if b && gamma.denom <= gamma.numer
    then
      Partial.Bind(
        SampleGammaLe1(Rationals.Int(1)),
        b' => GammaReductionLoop(b', Rationals.Rational(gamma.numer - gamma.denom, gamma.denom))
      )
    else
      Partial.Return((b, gamma))
  }

  ghost function SampleGammaLe1(gamma: Rationals.Rational): Partial.Hurd<bool>
  {
    if 0 <= gamma.numer <= gamma.denom
    then Partial.Bind(
           GammaLe1Loop(gamma, (true, 0)),
           (ak: (bool, nat)) => Partial.Return(ak.1 % 2 == 1)
         )
    else Partial.Return(false) // to keep this function total, we return a dummy value here
  }

  ghost function GammaLe1Loop(gamma: Rationals.Rational, ak: (bool, nat)): Partial.Hurd<(bool, nat)>
    requires 0 <= gamma.numer <= gamma.denom
  {
    assume {:axiom} false; // assume termination
    Partial.Bind(
      WhileAndUntil.ProbWhile(
        (ak: Partial.Wrap<(bool, nat)>) => ak.Satisfies((x: (bool, nat)) => x.0),
        (ak: Partial.Wrap<(bool, nat)>) =>
          match ak
          case Terminating(ak) => GammaLe1LoopIter(gamma, ak)
          case Diverging => Partial.Diverge(),
        Partial.Terminating(ak)
      ),
      (ak: Partial.Wrap<(bool, nat)>) => Monad.Return(ak)
    )
  }

  ghost function GammaLe1LoopIter(gamma: Rationals.Rational, ak: (bool, nat)): Partial.Hurd<(bool, nat)>
    requires 0 <= gamma.numer <= gamma.denom
  {
    Partial.Bind(
      BernoulliModel.Sample(gamma.numer, (ak.1 + 1) * gamma.denom),
      (a': bool) => Partial.Return((a', ak.1 + 1))
    )
  }
}

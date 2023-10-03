/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

include "../../Math/Helper.dfy"
include "../../ProbabilisticProgramming/Monad.dfy"
include "../../ProbabilisticProgramming/Independence.dfy"
include "../../ProbabilisticProgramming/RandomNumberGenerator.dfy"
include "../../ProbabilisticProgramming/WhileAndUntil.dfy"
include "Model.dfy"

module GeometricCorrectness {
  import Helper
  import WhileAndUntil
  import Independence
  import Monad
  import RandomNumberGenerator
  import Model = GeometricModel

  /*******
   Lemmas
  *******/

  // Equation (4.19)
  lemma SampleIsIndepFn()
    ensures Independence.IsIndepFn(Model.Sample())
  {
    var fst := (t: (bool, int)) => t.0;
    var f := (t: (bool, int)) => Monad.Return(t.1 - 1);
    assert WhileAndUntil.ProbWhileTerminates(Model.SampleIter, fst) by {
      Model.ProbWhileSampleTerminates();
    }
    var g := WhileAndUntil.ProbWhile(fst, Model.SampleIter, (true, 0));
    assert Independence.IsIndepFn(Monad.Bind(g, f)) by {
      assert Independence.IsIndepFn(g) by {
        assert forall a' :: Independence.IsIndepFn(Model.SampleIter(a'));
        WhileAndUntil.EnsureProbWhileIsIndepFn(fst, Model.SampleIter, (true, 0));
      }
      assert forall t :: Independence.IsIndepFn(f(t)) by {
        forall t ensures Independence.IsIndepFn(f(t)) {
          Independence.ReturnIsIndepFn(t.1 - 1);
        }
      }
      Independence.IndepFnIsCompositional(g, f);
    }
  }

  // Equation (4.20)
  lemma {:axiom} SampleCorrectness(n: nat)
    ensures
      var e := iset s | Model.Sample()(s).0 == n;
      && e in RandomNumberGenerator.event_space
      && RandomNumberGenerator.mu(e) == Helper.RealPower(1.0 / 2.0, n + 1)
}
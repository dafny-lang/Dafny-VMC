/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module Uniform.Model {
  import MeasureTheory
  import Helper
  import RandomNumberGenerator
  import Quantifier
  import Monad
  import Partial
  import Independence
  import WhileAndUntil
  import UniformPowerOfTwo

  // Definition 49
  ghost function Sample(n: nat): Partial.Hurd<nat>
    requires n > 0
  {
    SampleTerminates(n);
    WhileAndUntil.ProbUntil(Proposal(n), Accept(n))
  }

  function Proposal(n: nat): Monad.Hurd<nat>
    requires n > 0
  {
    UniformPowerOfTwo.Model.Sample(2 * n)
  }

  function Accept(n: nat): nat -> bool
    requires n > 0
  {
    (m: nat) => m < n
  }

  ghost function IntervalSample(a: int, b: int): (f: Partial.Hurd<int>)
    requires a < b
  {
    (s: RandomNumberGenerator.RNG) =>
      var (x, s') := Sample(b - a)(s);
      (x.Map(x => a + x), s')
  }

  lemma SampleTerminates(n: nat)
    requires n > 0
    ensures
      && Independence.IsIndepFn(Proposal(n))
      && Quantifier.ExistsStar(WhileAndUntil.ProposalIsAccepted(Proposal(n), Accept(n)))
      && WhileAndUntil.ProbUntilTerminates(Proposal(n), Accept(n))
  {
    assert Independence.IsIndepFn(Proposal(n)) by {
      UniformPowerOfTwo.Correctness.SampleIsIndepFn(2 * n);
    }
    var e := iset s | WhileAndUntil.ProposalIsAccepted(Proposal(n), Accept(n))(s);
    assert e in RandomNumberGenerator.event_space by {
      assert e == MeasureTheory.PreImage(s => UniformPowerOfTwo.Model.Sample(2 * n)(s).0, (iset m: nat | m < n));
      assert MeasureTheory.PreImage(s => UniformPowerOfTwo.Model.Sample(2 * n)(s).0, (iset m: nat | m < n)) in RandomNumberGenerator.event_space by {
        assert Independence.IsIndepFn(UniformPowerOfTwo.Model.Sample(2 * n)) by {
          UniformPowerOfTwo.Correctness.SampleIsIndepFn(2 * n);
        }
        assert MeasureTheory.IsMeasurable(RandomNumberGenerator.event_space, MeasureTheory.natEventSpace, s => UniformPowerOfTwo.Model.Sample(2 * n)(s).0) by {
          Independence.IsIndepFnImpliesFstMeasurableNat(UniformPowerOfTwo.Model.Sample(2 * n));
        }
      }
    }
    assert Quantifier.ExistsStar(WhileAndUntil.ProposalIsAccepted(Proposal(n), Accept(n))) by {
      assert RandomNumberGenerator.mu(e) > 0.0 by {
        assert e == (iset s | UniformPowerOfTwo.Model.Sample(2 * n)(s).0 < n);
        assert n <= Helper.Power(2, Helper.Log2Floor(2 * n)) by {
          Helper.NLtPower2Log2FloorOf2N(n);
        }
        calc {
          RandomNumberGenerator.mu(e);
        == { UniformPowerOfTwo.Correctness.UnifCorrectness2Inequality(2 * n, n); }
          n as real / (Helper.Power(2, Helper.Log2Floor(2 * n)) as real);
        >
          0.0;
        }
      }
    }
    assert WhileAndUntil.ProbUntilTerminates(Proposal(n), Accept(n)) by {
      WhileAndUntil.EnsureProbUntilTerminates(Proposal(n), Accept(n));
    }
  }
}

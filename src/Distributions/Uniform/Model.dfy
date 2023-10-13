/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module Uniform.Model {
  import Measures
  import Helper
  import Random
  import Quantifier
  import Monad
  import Independence
  import Loops
  import UniformPowerOfTwo

  // Definition 49
  function Sample(n: nat): Monad.Hurd<nat>
    requires n > 0
  {
    SampleTerminates(n);
    Loops.Until(Proposal(n), Accept(n))
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

  function IntervalSample(a: int, b: int): (f: Monad.Hurd<int>)
    requires a < b
  {
    (s: Random.Bitstream) =>
      var (x, s') := Sample(b - a)(s);
      (a + x, s')
  }

  lemma SampleTerminates(n: nat)
    requires n > 0
    ensures
      && Independence.IsIndep(Proposal(n))
      && Quantifier.WithPosProb(Loops.ProposalIsAccepted(Proposal(n), Accept(n)))
      && Loops.UntilTerminates(Proposal(n), Accept(n))
  {
    assert Independence.IsIndep(Proposal(n)) by {
      UniformPowerOfTwo.Correctness.SampleIsIndep(2 * n);
    }
    var e := iset s | Loops.ProposalIsAccepted(Proposal(n), Accept(n))(s);
    assert e in Random.eventSpace by {
      assert e == Measures.PreImage(s => UniformPowerOfTwo.Model.Sample(2 * n)(s).0, (iset m: nat | m < n));
      assert Measures.PreImage(s => UniformPowerOfTwo.Model.Sample(2 * n)(s).0, (iset m: nat | m < n)) in Random.eventSpace by {
        assert Independence.IsIndep(UniformPowerOfTwo.Model.Sample(2 * n)) by {
          UniformPowerOfTwo.Correctness.SampleIsIndep(2 * n);
        }
        assert Measures.IsMeasurable(Random.eventSpace, Measures.natEventSpace, s => UniformPowerOfTwo.Model.Sample(2 * n)(s).0) by {
          Independence.IsIndepImpliesFstMeasurableNat(UniformPowerOfTwo.Model.Sample(2 * n));
        }
      }
    }
    assert Quantifier.WithPosProb(Loops.ProposalIsAccepted(Proposal(n), Accept(n))) by {
      assert Random.prob(e) > 0.0 by {
        assert e == (iset s | UniformPowerOfTwo.Model.Sample(2 * n)(s).0 < n);
        assert n <= Helper.Power(2, Helper.Log2Floor(2 * n)) by {
          Helper.NLtPower2Log2FloorOf2N(n);
        }
        calc {
          Random.prob(e);
        == { UniformPowerOfTwo.Correctness.UnifCorrectness2Inequality(2 * n, n); }
          n as real / (Helper.Power(2, Helper.Log2Floor(2 * n)) as real);
        >
          0.0;
        }
      }
    }
    assert Loops.UntilTerminates(Proposal(n), Accept(n)) by {
      Loops.EnsureUntilTerminates(Proposal(n), Accept(n));
    }
  }
}

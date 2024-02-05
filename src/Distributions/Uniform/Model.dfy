/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module Uniform.Model {
  import Measures
  import NatArith
  import Rand
  import Quantifier
  import Monad
  import Independence
  import Loops
  import UniformPowerOfTwo

  /************
   Definitions
  ************/

  // Definition 49
  opaque ghost function Sample(n: nat): Monad.Hurd<nat>
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

  ghost function IntervalSample(a: int, b: int): (f: Monad.Hurd<int>)
    requires a < b
  {
    Monad.Map(Sample(b - a), x => a + x)
  }

  /*******
   Lemmas
  *******/

  lemma SampleTerminates(n: nat)
    requires n > 0
    ensures
      && Independence.IsIndep(Proposal(n))
      && Quantifier.WithPosProb(Loops.ProposalIsAccepted(Proposal(n), Accept(n)))
      && Loops.UntilTerminatesAlmostSurely(Proposal(n), Accept(n))
  {
    assert Independence.IsIndep(Proposal(n)) by {
      UniformPowerOfTwo.Correctness.SampleIsIndep(2 * n);
    }
    var e := iset s | Loops.ProposalIsAccepted(Proposal(n), Accept(n))(s);
    assert e in Rand.eventSpace by {
      var ltN := iset m: nat | m < n;
      var resultsLtN := Monad.ResultsWithValueIn(ltN);
      assert e == Measures.PreImage(UniformPowerOfTwo.Model.Sample(2 * n), resultsLtN);
      assert Measures.PreImage(UniformPowerOfTwo.Model.Sample(2 * n), resultsLtN) in Rand.eventSpace by {
        assert Independence.IsIndep(UniformPowerOfTwo.Model.Sample(2 * n)) by {
          UniformPowerOfTwo.Correctness.SampleIsIndep(2 * n);
        }
        assert Measures.IsMeasurable(Rand.eventSpace, Monad.natResultEventSpace, UniformPowerOfTwo.Model.Sample(2 * n)) by {
          Independence.IsIndepImpliesMeasurableNat(UniformPowerOfTwo.Model.Sample(2 * n));
        }
        assert resultsLtN in Monad.natResultEventSpace by {
          Monad.LiftInEventSpaceToResultEventSpace(ltN, Measures.natEventSpace);
        }
      }
    }
    assert Quantifier.WithPosProb(Loops.ProposalIsAccepted(Proposal(n), Accept(n))) by {
      assert Rand.prob(e) > 0.0 by {
        assert e == (iset s | UniformPowerOfTwo.Model.Sample(2 * n)(s).value < n);
        assert n <= NatArith.Power(2, NatArith.Log2Floor(2 * n)) by {
          NatArith.NLtPower2Log2FloorOf2N(n);
        }
        calc {
          Rand.prob(e);
        == { UniformPowerOfTwo.Correctness.UnifCorrectness2Inequality(2 * n, n); }
          n as real / (NatArith.Power(2, NatArith.Log2Floor(2 * n)) as real);
        >
          0.0;
        }
      }
    }
    assert Loops.UntilTerminatesAlmostSurely(Proposal(n), Accept(n)) by {
      Loops.EnsureUntilTerminates(Proposal(n), Accept(n));
    }
  }

  lemma SampleBound(n: nat, s: Rand.Bitstream)
    requires n > 0
    requires Sample(n)(s).Result?
    ensures 0 <= Sample(n)(s).value < n
  {
    reveal Sample();
    SampleTerminates(n);
    Loops.UntilResultIsAccepted(Proposal(n), Accept(n), s);
  }

  lemma IntervalSampleBound(a: int, b: int, s: Rand.Bitstream)
    requires a < b
    requires IntervalSample(a, b)(s).Result?
    ensures a <= IntervalSample(a, b)(s).value < b
  {
    SampleBound(b-a, s);
  }

}

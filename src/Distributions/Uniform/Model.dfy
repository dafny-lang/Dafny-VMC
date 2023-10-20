/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module Uniform.Model {
  import Measures
  import Helper
  import Rand
  import Quantifier
  import Monad
  import Independence
  import Loops
  import UniformPowerOfTwo

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
    (s: Rand.Bitstream) =>
      var Result(x, s') := Sample(b - a)(s);
      Monad.Result(a + x, s')
  }

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
      assert e == Measures.PreImage(s => UniformPowerOfTwo.Model.Sample(2 * n)(s).value, (iset m: nat | m < n));
      assert Measures.PreImage(s => UniformPowerOfTwo.Model.Sample(2 * n)(s).value, (iset m: nat | m < n)) in Rand.eventSpace by {
        assert Independence.IsIndep(UniformPowerOfTwo.Model.Sample(2 * n)) by {
          UniformPowerOfTwo.Correctness.SampleIsIndep(2 * n);
        }
        assert Measures.IsMeasurable(Rand.eventSpace, Measures.natEventSpace, s => UniformPowerOfTwo.Model.Sample(2 * n)(s).value) by {
          Independence.IsIndepImpliesValueMeasurableNat(UniformPowerOfTwo.Model.Sample(2 * n));
        }
      }
    }
    assert Quantifier.WithPosProb(Loops.ProposalIsAccepted(Proposal(n), Accept(n))) by {
      assert Rand.prob(e) > 0.0 by {
        assert e == (iset s | UniformPowerOfTwo.Model.Sample(2 * n)(s).value < n);
        assert n <= Helper.Power(2, Helper.Log2Floor(2 * n)) by {
          Helper.NLtPower2Log2FloorOf2N(n);
        }
        calc {
          Rand.prob(e);
        == { UniformPowerOfTwo.Correctness.UnifCorrectness2Inequality(2 * n, n); }
          n as real / (Helper.Power(2, Helper.Log2Floor(2 * n)) as real);
        >
          0.0;
        }
      }
    }
    assert Loops.UntilTerminatesAlmostSurely(Proposal(n), Accept(n)) by {
      Loops.EnsureUntilTerminates(Proposal(n), Accept(n));
    }
  }

  lemma SampleUnroll(n: nat, s: Rand.Bitstream)
    requires n > 0
    ensures Sample(n)(s) == Monad.Bind(Proposal(n), (x: nat) => if Accept(n)(x) then Monad.Return(x) else Sample(n))(s)
  {
    SampleTerminates(n);
    reveal Sample();
    Loops.UntilUnroll(Proposal(n), Accept(n), s);
  }
}

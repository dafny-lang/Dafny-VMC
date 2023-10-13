/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module Uniform.Correctness {
  import Helper
  import Monad
  import Independence
  import Random
  import Quantifier
  import Loops
  import Measures
  import UniformPowerOfTwo
  import Model

  /************
   Definitions
  ************/

  ghost function SampleEquals(n: nat, i: nat): iset<Random.Bitstream>
    requires 0 <= i < n
  {
    iset s | Model.Sample(n)(s).0 == i
  }

  /*******
   Lemmas
  *******/

  // Correctness theorem for Model.Sample
  // Equation (4.12) / PROB_BERN_UNIFORM
  lemma UniformFullCorrectness(n: nat, i: nat)
    requires 0 <= i < n
    ensures SampleEquals(n, i) in Random.eventSpace
    ensures Random.Prob(SampleEquals(n, i)) == 1.0 / (n as real)
  {
    var equalsI := (x: nat) => x == i;

    assert Independence.IsIndep(Model.Proposal(n)) && Quantifier.WithPosProb(Loops.ProposalIsAccepted(Model.Proposal(n), Model.Accept(n))) by {
      Model.SampleTerminates(n);
    }

    Loops.UntilProbabilityFraction(Model.Proposal(n), Model.Accept(n), equalsI);
    var eventResultEqualsI := Loops.UntilLoopResultHasProperty(Model.Proposal(n), Model.Accept(n), equalsI);
    var eventProposalAcceptedAndEqualsI := Loops.ProposalIsAcceptedAndHasProperty(Model.Proposal(n), Model.Accept(n), equalsI);
    var proposalAccepted := Loops.ProposalAcceptedEvent(Model.Proposal(n), Model.Accept(n));

    assert Fraction: Random.Prob(eventResultEqualsI) == Random.Prob(eventProposalAcceptedAndEqualsI) / Random.Prob(proposalAccepted);

    assert Eq: eventResultEqualsI == SampleEquals(n, i) by {
      forall s ensures s in eventResultEqualsI <==> s in SampleEquals(n, i) {
        assert s in eventResultEqualsI <==> s in SampleEquals(n, i);
      }
    }

    assert SampleEquals(n, i) in Random.eventSpace by {
      reveal Eq;
    }

    assert Random.Prob(SampleEquals(n, i)) == 1.0 / (n as real) by {
      calc {
        Random.Prob(SampleEquals(n, i));
        { reveal Eq; }
        Random.Prob(eventResultEqualsI);
        { reveal Fraction; }
        Random.Prob(eventProposalAcceptedAndEqualsI) / Random.Prob(proposalAccepted);
        { ProbabilityProposalAcceptedAndEqualsI(n, i); }
        (1.0 / (Helper.Power(2, Helper.Log2Floor(2 * n)) as real)) / Random.Prob(proposalAccepted);
        { ProbabilityProposalAccepted(n); }
        (1.0 / (Helper.Power(2, Helper.Log2Floor(2 * n)) as real)) / ((n as real) / (Helper.Power(2, Helper.Log2Floor(2 * n)) as real));
        { Helper.SimplifyFractions(1.0, n as real, Helper.Power(2, Helper.Log2Floor(2 * n)) as real); }
        1.0 / (n as real);
      }
    }
  }

  lemma ProbabilityProposalAcceptedAndEqualsI(n: nat, i: nat)
    requires 0 <= i < n
    ensures
      var e := Loops.ProposalIsAcceptedAndHasProperty(Model.Proposal(n), Model.Accept(n), (x: nat) => x == i);
      Random.Prob(e) == 1.0 / (Helper.Power(2, Helper.Log2Floor(2 * n)) as real)
  {
    var e := Loops.ProposalIsAcceptedAndHasProperty(Model.Proposal(n), Model.Accept(n), (x: nat) => x == i);
    assert i < Helper.Power(2, Helper.Log2Floor(2 * n)) by {
      calc {
        i;
      <
        n;
      < { Helper.Power2OfLog2Floor(n); }
        Helper.Power(2, Helper.Log2Floor(n) + 1);
      == { Helper.Log2FloorDef(n); }
        Helper.Power(2, Helper.Log2Floor(2 * n));
      }
    }
    assert e == (iset s | UniformPowerOfTwo.Model.Sample(2 * n)(s).0 == i) by {
      forall s ensures s in e <==> UniformPowerOfTwo.Model.Sample(2 * n)(s).0 == i {}
    }
    UniformPowerOfTwo.Correctness.UnifCorrectness2(2 * n, i);
  }

  lemma ProbabilityProposalAccepted(n: nat)
    requires n >= 1
    ensures
      Random.Prob(Loops.ProposalAcceptedEvent(Model.Proposal(n), Model.Accept(n))) == (n as real) / (Helper.Power(2, Helper.Log2Floor(2 * n)) as real)
  {
    var e := Loops.ProposalAcceptedEvent(Model.Proposal(n), Model.Accept(n));
    assert n < Helper.Power(2, Helper.Log2Floor(2 * n)) by { Helper.NLtPower2Log2FloorOf2N(n); }
    assert Equal: e == (iset s | UniformPowerOfTwo.Model.Sample(2 * n)(s).0 < n) by {
      forall s ensures s in e <==> UniformPowerOfTwo.Model.Sample(2 * n)(s).0 < n {
        calc {
          s in e;
          Model.Accept(n)(Model.Proposal(n)(s).0);
          UniformPowerOfTwo.Model.Sample(2 * n)(s).0 < n;
        }
      }
    }
    assert Random.Prob(Loops.ProposalAcceptedEvent(Model.Proposal(n), Model.Accept(n))) == (n as real) / (Helper.Power(2, Helper.Log2Floor(2 * n)) as real) by {
      calc {
        Random.Prob(e);
        { reveal Equal; }
        Random.Prob(iset s | UniformPowerOfTwo.Model.Sample(2 * n)(s).0 < n);
        { UniformPowerOfTwo.Correctness.UnifCorrectness2Inequality(2 * n, n); }
        (n as real) / (Helper.Power(2, Helper.Log2Floor(2 * n)) as real);
      }
    }
  }

  // Correctness theorem for Model.IntervalSample
  lemma UniformFullIntervalCorrectness(a: int, b: int, i: int)
    requires a <= i < b
    ensures
      var e := iset s | Model.IntervalSample(a, b)(s).0 == i;
      && e in Random.eventSpace
      && Random.Prob(e) == (1.0 / ((b-a) as real))
  {
    assert 0 <= i - a < b - a by {
      assert a <= i < b;
    }
    var e' := SampleEquals(b - a, i - a);
    assert e' in Random.eventSpace by { UniformFullCorrectness(b - a, i - a); }
    assert Random.Prob(e') == (1.0 / ((b-a) as real)) by { UniformFullCorrectness(b - a, i - a); }
    var e := iset s | Model.IntervalSample(a, b)(s).0 == i;
    assert e == e' by {
      forall s ensures Model.IntervalSample(a, b)(s).0 == i <==> Model.Sample(b-a)(s).0 == i - a {
        assert Model.IntervalSample(a, b)(s).0 == a + Model.Sample(b - a)(s).0;
      }
    }
  }

  // Equation (4.10)
  lemma SampleIsIndep(n: nat)
    requires n > 0
    ensures Independence.IsIndep(Model.Sample(n))
  {
    assert Independence.IsIndep(Model.Proposal(n)) by {
      UniformPowerOfTwo.Correctness.SampleIsIndep(2 * n);
    }
    assert Loops.UntilTerminates(Model.Proposal(n), Model.Accept(n)) by {
      Model.SampleTerminates(n);
    }
    Loops.UntilIsIndep(Model.Proposal(n), Model.Accept(n));
  }
}

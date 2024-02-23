/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module Uniform.Correctness {
  import NatArith
  import RealArith
  import Monad
  import Independence
  import Rand
  import Quantifier
  import Loops
  import Measures
  import Model

  /************
   Definitions
  ************/

  ghost function SampleEquals(n: nat, i: nat): iset<Rand.Bitstream>
    requires 0 <= i < n
  {
    iset s | Model.Sample(n)(s).Equals(i)
  }

  /*******
   Lemmas
  *******/

  // Correctness theorem for Model.Sample
  // Equation (4.12) / PROB_BERN_UNIFORM
  lemma {:axiom} UniformFullCorrectness(n: nat, i: nat)
    requires 0 <= i < n
    ensures SampleEquals(n, i) in Rand.eventSpace
    ensures Rand.prob(SampleEquals(n, i)) == 1.0 / (n as real)

  // Equation (4.10)
  lemma {:axiom} SampleIsIndep(n: nat)
    requires n > 0
    ensures Independence.IsIndep(Model.Sample(n))

  // Correctness theorem for Model.IntervalSample
  lemma UniformFullIntervalCorrectness(a: int, b: int, i: int)
    requires a <= i < b
    ensures
      var e := iset s | Model.IntervalSample(a, b)(s).Equals(i);
      && e in Rand.eventSpace
      && Rand.prob(e) == (1.0 / ((b-a) as real))
  {
    assert 0 <= i - a < b - a by {
      assert a <= i < b;
    }
    var e' := SampleEquals(b - a, i - a);
    assert e' in Rand.eventSpace by { UniformFullCorrectness(b - a, i - a); }
    assert Rand.prob(e') == (1.0 / ((b-a) as real)) by { UniformFullCorrectness(b - a, i - a); }
    var e := iset s | Model.IntervalSample(a, b)(s).Equals(i);
    assert e == e' by {
      forall s ensures Model.IntervalSample(a, b)(s).Equals(i) <==> Model.Sample(b-a)(s).Equals(i - a) {
        assert Model.IntervalSample(a, b)(s) == Model.Sample(b - a)(s).Map(x => a + x);
      }
    }
  }

  lemma IntervalSampleIsIndep(a: int, b: int)
    requires a < b
    ensures Independence.IsIndep(Model.IntervalSample(a, b))
  {
    SampleIsIndep(b-a);
    Independence.MapIsIndep(Model.Sample(b-a), x => a + x);
  }
}

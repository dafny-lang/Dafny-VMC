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
  import Measures
  import Model

  /************
   Definitions
  ************/

  function IntervalSampleIsIndepFunctionHelper(a: int, x: int): nat
    requires x-a >= 0
  {
    x-a
  }

  ghost function IntervalSampleIsIndepFunctionHelperLifted(a: int, A: iset<int>): iset<nat>
  {
    iset x: int | x in A && x-a >= 0 :: IntervalSampleIsIndepFunctionHelper(a, x)
  }

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
  lemma UniformFullCorrectness(n: nat, i: nat)
    requires 0 <= i < n
    ensures
      var e := iset s | Model.Sample(n)(s).Equals(i);
      e in Rand.eventSpace &&
      Rand.prob(e) == 1.0 / (n as real)
  {}

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

  lemma SampleIsIndepFunction(n: nat)
    requires n > 0
    ensures Independence.IsIndepFunction(Model.Sample(n))
  {}

  lemma IntervalSampleIsIndepFunction(a: int, b: int)
    requires a < b
    ensures Independence.IsIndepFunction(Model.IntervalSample(a, b))
  {
    forall A: iset<int>, E: iset<Rand.Bitstream> | E in Rand.eventSpace ensures Independence.IsIndepFunctionCondition(Model.IntervalSample(a, b), A, E) {
      var A': iset<nat> := IntervalSampleIsIndepFunctionHelperLifted(a, A);
      assert Measures.AreIndepEvents(Rand.eventSpace, Rand.prob, Monad.BitstreamsWithValueIn(Model.IntervalSample(a, b), A), Monad.BitstreamsWithRestIn(Model.IntervalSample(a, b), E)) by {
        assert Monad.BitstreamsWithValueIn(Model.IntervalSample(a, b), A) == Monad.BitstreamsWithValueIn(Model.Sample(b - a), A') by {
          forall s ensures s in Monad.BitstreamsWithValueIn(Model.IntervalSample(a, b), A) <==> s in Monad.BitstreamsWithValueIn(Model.Sample(b - a), A') {
            calc {
              s in Monad.BitstreamsWithValueIn(Model.IntervalSample(a, b), A);
              Monad.Map(Model.Sample(b - a), x => a + x)(s).value in A;
              Monad.Bind(Model.Sample(b - a), x => Monad.Return(a+x))(s).value in A;
              Model.Sample(b - a)(s).value + a in A;
              Model.Sample(b - a)(s).value in A';
              s in Monad.BitstreamsWithValueIn(Model.Sample(b - a), A');
            }
          }
        }
        assert Monad.BitstreamsWithRestIn(Model.IntervalSample(a, b), E) == Monad.BitstreamsWithRestIn(Model.Sample(b-a), E) by {
          forall s ensures s in Monad.BitstreamsWithRestIn(Model.IntervalSample(a, b), E) <==> s in Monad.BitstreamsWithRestIn(Model.Sample(b-a), E) {
            calc {
              s in Monad.BitstreamsWithRestIn(Model.IntervalSample(a, b), E);
              Monad.Map(Model.Sample(b - a), x => a + x)(s).rest in E;
              Monad.Bind(Model.Sample(b - a), x => Monad.Return(a+x))(s).rest in E;
              Model.Sample(b-a)(s).rest in E;
              s in Monad.BitstreamsWithRestIn(Model.Sample(b-a), E);
            }
          }
        }
        assert Independence.IsIndepFunctionCondition(Model.Sample(b - a), A', E) by {
          SampleIsIndepFunction(b-a);
        }
      }
    }
  }

  lemma SampleBound(n: nat, s: Rand.Bitstream)
    requires n > 0
    ensures 0 <= Model.Sample(n)(s).value < n
  {}

  lemma IntervalSampleBound(a: int, b: int, s: Rand.Bitstream)
    requires a < b
    ensures a <= Model.IntervalSample(a, b)(s).value < b
  {
    SampleBound(b-a, s);
  }

  lemma SampleIsMeasurePreserving(n: nat)
    requires n > 0
    ensures forall n | n > 0 :: Measures.IsMeasurePreserving(Rand.eventSpace, Rand.prob, Rand.eventSpace, Rand.prob, s => Model.Sample(n)(s).rest)
  {}

  lemma IntervalSampleIsMeasurePreserving(a: int, b: int)
    requires a < b
    ensures Measures.IsMeasurePreserving(Rand.eventSpace, Rand.prob, Rand.eventSpace, Rand.prob, s => Model.IntervalSample(a, b)(s).rest)
  {
    var f := s => Model.IntervalSample(a, b)(s).rest;
    var f' := s => Model.Sample(b-a)(s).rest;

    forall e: iset<Rand.Bitstream> | e in Rand.eventSpace ensures Measures.PreImage(f, e) == Measures.PreImage(f', e) {
      forall s ensures s in Measures.PreImage(f, e) <==> s in Measures.PreImage(f', e) {
        calc {
          s in Measures.PreImage(f, e);
          f(s) in e;
          Model.IntervalSample(a, b)(s).rest in e;
          Model.Sample(b-a)(s).rest in e;
          f'(s) in e;
          s in Measures.PreImage(f', e);
        }
      }
    }

    assert Measures.IsMeasurable(Rand.eventSpace, Rand.eventSpace, f) by {
      forall e: iset<Rand.Bitstream> | e in Rand.eventSpace ensures Measures.PreImage(f, e) in Rand.eventSpace {
        assert Measures.PreImage(f, e) == Measures.PreImage(f', e);
        SampleIsMeasurePreserving(b-a);
      }
    }

    forall e | e in Rand.eventSpace ensures Rand.prob(Measures.PreImage(f, e)) == Rand.prob(e) {
      assert Measures.PreImage(f, e) == Measures.PreImage(f', e);
      SampleIsMeasurePreserving(b-a);
    }

  }
}

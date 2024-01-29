/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module FisherYates.Correctness {
  import Model
  import Rand
  import Uniform
  import Monad
  import Independence
  import RealArith
  import Measures
  import Loops
  import Permutations

  /*******
   Lemmas
  *******/

  lemma CorrectnessFisherYates<T(!new)>(xs: seq<T>, p: seq<T>)
    requires Permutations.IsPermutationOf(p, xs)
    ensures
      var e := iset s | Model.Shuffle(xs)(s).Equals(p);
      && e in Rand.eventSpace
      && Rand.prob(e) == 1.0 / (Permutations.NumberOfPermutationsOf(xs) as real)
  {
    var e := iset s | Model.Shuffle(xs)(s).Equals(p);
    var e' := iset s | Model.Shuffle(xs, 0)(s).Result? && Model.Shuffle(xs, 0)(s).value[0..] == p[0..];
    assert e == e';
    CorrectnessFisherYatesGeneral(xs, p, 0);
  }

  lemma {:axiom} CorrectnessFisherYatesGeneral<T(!new)>(xs: seq<T>, p: seq<T>, i: nat)
    requires i <= |xs|
    requires i <= |p|
    requires Permutations.IsPermutationOf(p[i..], xs[i..])
    decreases |xs| - i
    ensures
      var e := iset s | Model.Shuffle(xs, i)(s).Result? && Model.Shuffle(xs, i)(s).value[i..] == p[i..];
      && e in Rand.eventSpace
      && Rand.prob(e) == 1.0 / (Permutations.NumberOfPermutationsOf(xs[i..]) as real)
  /*  {
     Permutations.PermutationsPreserveCardinality(p[i..], xs[i..]);
     var e := iset s | Model.Shuffle(xs, i)(s).Result? && Model.Shuffle(xs, i)(s).value[i..] == p[i..];
     if |xs[i..]| <= 1 {
       assert e == Measures.SampleSpace() by {
         forall s
           ensures s in e
         {
           calc {
             s in e;
             Model.Shuffle(xs, i)(s).Result? && Model.Shuffle(xs, i)(s).value[i..] == p[i..];
             { assert Model.Shuffle(xs, i)(s) == Monad.Return(xs)(s); }
             Monad.Return(xs)(s).Result? && Monad.Return(xs)(s).value[i..] == p[i..];
             { assert Monad.Return(xs)(s).value == xs; }
             xs[i..] == p[i..];
             if |xs[i..]| == 0 then [] == p[i..] else [xs[i]] == p[i..];
             { assert |xs[i..]| == |p[i..]|; }
             if |xs[i..]| == 0 then true else [xs[i]] == [p[i]];
             { assert multiset(p[i..]) == multiset(xs[i..]); }
             true;
           }
         }
       }
       Rand.ProbIsProbabilityMeasure();
       assert Measures.IsProbability(Rand.eventSpace, Rand.prob);
     } else {
       var h := Uniform.Model.IntervalSample(i, |xs|);
       assert HIsIndependent: Independence.IsIndep(h) by {
         Uniform.Correctness.IntervalSampleIsIndep(i, |xs|);
       }
       var multiplicity := multiset(xs[i..])[xs[i]];
       var length := |xs[i..]|;
       var A := iset j | i <= j < |xs| && xs[j] == p[i];
       assert A != iset{} by {
         assume {:axiom} false;
         assert Permutations.IsPermutationOf(p[i..], xs[i..]);
       }
       var j :| j in A;
       var ys := Permutations.Swap(xs, i, j);
       var e' := iset s | Model.Shuffle(ys, i+1)(s).Result? && Model.Shuffle(ys, i+1)(s).value[i+1..] == p[i+1..];
       assume {:axiom} false;
       /*
     assert DecomposeE: e == (iset s | s in Monad.BitstreamsWithValueIn(h, A) && s in Monad.BitstreamsWithRestIn(h, e')) by {
       assume {:axiom} false;
     } 
            calc {
       Rand.prob(e);
       Rand.prob(iset s | Model.Shuffle(xs, i)(s).Result? && Model.Shuffle(xs, i)(s).value[i..] == p[i..]);
       { reveal DecomposeE; }
       Rand.prob(iset s | s in Monad.BitstreamsWithValueIn(h, A) && s in Monad.BitstreamsWithRestIn(h, e'));
       { reveal HIsIndependent; Independence.ResultsIndependent(h, A, e'); }
       Rand.prob(iset s | s in Monad.BitstreamsWithValueIn(h, A)) * Rand.prob(e');
       { assume {:axiom} false; }
       //{ CorrectnessMultiset(xs, p[i], i); CorrectnessFisherYatesGeneral(xs, p, i+1); }
       (multiplicity as real / length as real) * (1.0 / (NumberOfPermutationsOf(xs[i+1..]) as real));
       { assume {:axiom} false; }
       (1.0 / ((length as real) / (multiplicity as real))) *  (1.0 / (NumberOfPermutationsOf(xs[i+1..]) as real));
       { assume {:axiom} false; }
       (1.0 / ((length / multiplicity) as real)) *  (1.0 / (NumberOfPermutationsOf(xs[i+1..]) as real));
       { assume {:axiom} false; assert 1.0 * 1.0 == 1.0; assert ((length / multiplicity) as real) * (NumberOfPermutationsOf(xs[i+1..]) as real) == (((length / multiplicity) * NumberOfPermutationsOf(xs[i+1..])) as real); }
       1.0 / (((length / multiplicity) * NumberOfPermutationsOf(xs[i+1..])) as real);    
       { assume {:axiom} false; assert xs[i+1..] == xs[i..][1..]; }        
       1.0 / (((length / multiplicity) * NumberOfPermutationsOf(xs[i..][1..])) as real);  
       { assume {:axiom} false; }      
       1.0 / (NumberOfPermutationsOf(xs[i..]) as real);
     } */
     }
   } */

  lemma {:axiom} CorrectnessMultiset<T>(xs: seq<T>, x: T, i: nat := 0)
    requires i <= |xs| - 1
    decreases |xs| - i
    ensures
      var A := iset j: int | i <= j < |xs| && xs[j] == x;
      var e := Monad.BitstreamsWithValueIn(Uniform.Model.IntervalSample(i, |xs|), A);
      var multiplicity := multiset(xs[i..])[x];
      var length := |xs[i..]|;
      && e in Rand.eventSpace
      && Rand.prob(e) == (multiplicity as real) / (length as real)
  /*  {
     var A := iset j: int | i <= j < |xs| && xs[j] == x;
     var e := Monad.BitstreamsWithValueIn(Uniform.Model.IntervalSample(i, |xs|), A);
     var multiplicity := multiset(xs[i..])[x];
     var length := |xs[i..]|;
     if i == |xs| - 1 {
       assert length == 1;
       if xs[i] == x {
         assert A == iset{ |xs| - 1 };
         assert multiplicity == 1;
         Uniform.Correctness.UniformFullIntervalCorrectness(i, |xs|, i);
       } else {
         assert A == iset{};
         assert e == iset{};
         assert multiplicity == 0;
         Rand.ProbIsProbabilityMeasure();
         assert Measures.IsPositive(Rand.eventSpace, Rand.prob);
       }
     } else {
       var A' := iset j: int | i+1 <= j < |xs| && xs[j] == x;
       var e' := Monad.BitstreamsWithValueIn(Uniform.Model.IntervalSample(i+1, |xs|), A');
       assert e'Equality: e' == Monad.BitstreamsWithValueIn(Uniform.Model.IntervalSample(i, |xs|), A') by {
         assume {:axiom} false;
       }
       var e'':= (iset s | Uniform.Model.IntervalSample(i, |xs|)(s).Equals(i as int));
       var multiplicity' := multiset(xs[i+1..])[x];
       var length' := |xs[i+1..]|;
       assert InductionHypothesis: e' in Rand.eventSpace && Rand.prob(e') == (multiplicity' as real) / (length' as real) by {
         CorrectnessMultiset(xs, x, i+1);
       }
       assert length == 1 + length';
       if xs[i] == x {
         assert multiplicity == 1 + multiplicity' by {
           calc {
             multiplicity;
             multiset(xs[i..])[x];
             { assert xs[i..] == [xs[i]] + xs[i+1..]; }
             multiset([xs[i]] + xs[i+1..])[x];
             (multiset([xs[i]]) + multiset(xs[i+1..]))[x];
             multiset([xs[i]])[x] + multiset(xs[i+1..])[x];
             1 + multiset(xs[i+1..])[x];
             1 + multiplicity';
           }
         }
         calc {
           e;
           Monad.BitstreamsWithValueIn(Uniform.Model.IntervalSample(i, |xs|), A);
           { assert A == A' + iset{i as int}; }
           Monad.BitstreamsWithValueIn(Uniform.Model.IntervalSample(i, |xs|), A' + iset{i as int});
           { Monad.BitstreamsWithValueInJoin(Uniform.Model.IntervalSample(i, |xs|), A', iset{i as int}); }
           Monad.BitstreamsWithValueIn(Uniform.Model.IntervalSample(i, |xs|), A') + Monad.BitstreamsWithValueIn(Uniform.Model.IntervalSample(i, |xs|), iset{i as int});
           { assume {:axiom} false; }
           Monad.BitstreamsWithValueIn(Uniform.Model.IntervalSample(i+1, |xs|), A') + (iset s | Uniform.Model.IntervalSample(i, |xs|)(s).Equals(i as int));
           e' + e'';
         }
         assert e''inEventSpace: e'' in Rand.eventSpace by {
           Uniform.Correctness.UniformFullIntervalCorrectness(i, |xs|, i);
         }
         assert MultProb: Rand.prob(e' + e'') == Rand.prob(e') + Rand.prob(e'') by {
           assume {:axiom} e' * e'' == iset{};
           reveal e''inEventSpace;
           reveal InductionHypothesis;
           Rand.ProbIsProbabilityMeasure();
           Measures.MeasureOfDisjointUnionIsSum(Rand.eventSpace, Rand.prob, e', e'');
         }
         calc {
           Rand.prob(e);
           Rand.prob(e' + e'');
           { reveal MultProb; }
           Rand.prob(e') + Rand.prob(e'');
           { reveal InductionHypothesis; Uniform.Correctness.UniformFullIntervalCorrectness(i, |xs|, i as int); }
           ((multiplicity' as real) / (length' as real)) + (1.0 / (|xs| - i) as real);
           ((multiplicity' as real) / (length' as real)) + 1.0 / length as real;
           ((multiplicity' as real) / (length' as real)) + 1.0 / (1 + length') as real;
           { assume {:axiom} false; }
           ((1 + multiplicity') as real) / ((1 + length') as real);
           (multiplicity as real) / (length as real);
         }
       } else {
         assert multiplicity == multiplicity' by {
           calc {
             multiplicity;
             multiset(xs[i..])[x];
             { assert xs[i..] == [xs[i]] + xs[i+1..]; }
             multiset([xs[i]] + xs[i+1..])[x];
             (multiset([xs[i]]) + multiset(xs[i+1..]))[x];
             multiset([xs[i]])[x] + multiset(xs[i+1..])[x];
             multiset(xs[i+1..])[x];
             multiplicity';
           }
         }
         calc {
           e;
           Monad.BitstreamsWithValueIn(Uniform.Model.IntervalSample(i, |xs|), A);
           { assert A == A'; }
           Monad.BitstreamsWithValueIn(Uniform.Model.IntervalSample(i, |xs|), A');
           { reveal e'Equality; }
           e';
         }
         calc {
           Rand.prob(e);
           Rand.prob(e');
           { reveal InductionHypothesis; }
           (multiplicity' as real) / (length' as real);
           { assume {:axiom} false; }
           (multiplicity' as real) / ((1 + length') as real);
           (multiplicity as real) / (length as real);
         }
       }
     }
   } */



}
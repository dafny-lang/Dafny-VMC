module Series {
  import NatArith
  import RealArith
  import Reals
  import Sequences
  import Limits

  function SumFromTo(sequence: nat -> real, start: nat, end: nat): real
    decreases end - start
  {
    if end <= start then 0.0 else sequence(start) + SumFromTo(sequence, start + 1, end)
  }

  function SumTo(sequence: nat -> real, end: nat): real {
    SumFromTo(sequence, 0, end)
  }

  function PartialSums(sequence: nat -> real): nat -> real {
    (n: nat) => SumTo(sequence, n)
  }

  ghost predicate SumsTo(summands: nat -> real, sum: real) {
    Limits.ConvergesTo(PartialSums(summands), sum)
  }

  ghost predicate IsSummable(summands: nat -> real) {
    exists sum: real :: SumsTo(summands, sum)
  }

  ghost function Sum(summands: nat -> real): real
    requires IsSummable(summands)
  {
    Limits.Limit(PartialSums(summands))
  }

  // This would be trivial if Dafny had function extensionality
  lemma SumFromToOfEqualsIsEqual(s1: nat -> real, s2: nat -> real, start: nat, end: nat)
    decreases end - start
    requires forall n: nat | start <= n < end :: s1(n) == s2(n)
    ensures SumFromTo(s1, start, end) == SumFromTo(s2, start, end)
  {
    if end <= start {
      calc {
        SumFromTo(s1, start, end);
        0.0;
        SumFromTo(s2, start, end);
      }
    } else {
      calc {
        SumFromTo(s1, start, end);
        s1(start) + SumFromTo(s1, start + 1, end);
        s2(start) + SumFromTo(s1, start + 1, end);
        { SumFromToOfEqualsIsEqual(s1, s2, start + 1, end); }
        s2(start) + SumFromTo(s1, start + 1, end);
        SumFromTo(s2, start, end);
      }
    }
  }

  // This would be trivial if Dafny had function extensionality
  lemma SumOfEqualsIsEqual(summands1: nat -> real, summands2: nat -> real, sum: real)
    requires forall n: nat :: summands1(n) == summands2(n)
    requires SumsTo(summands1, sum)
    ensures SumsTo(summands2, sum)
  {
    forall n: nat ensures PartialSums(summands1)(n) == PartialSums(summands2)(n) {
      calc {
        PartialSums(summands1)(n);
        SumTo(summands1, n);
        { SumFromToOfEqualsIsEqual(summands1, summands2, 0, n); }
        SumTo(summands2, n);
        PartialSums(summands2)(n);
      }
    }
    Limits.LimitOfEqualsIsEqual(PartialSums(summands1), PartialSums(summands2), sum);
  }

  lemma SumIsUnique(summands: nat -> real, sum1: real, sum2: real)
    requires SumsTo(summands, sum1)
    requires SumsTo(summands, sum2)
    ensures sum1 == sum2
  {
    Limits.LimitIsUnique(PartialSums(summands), sum1, sum2);
  }

  lemma SumIsUniqueAuto(summands: nat -> real)
    ensures forall sum1: real, sum2: real :: SumsTo(summands, sum1) && SumsTo(summands, sum2) ==> sum1 == sum2
  {
    forall sum1: real, sum2: real ensures SumsTo(summands, sum1) && SumsTo(summands, sum2) ==> sum1 == sum2 {
      if SumsTo(summands, sum1) && SumsTo(summands, sum2) {
        SumIsUnique(summands, sum1, sum2);
      }
    }
  }

  lemma SumsToImpliesSumIs(summands: nat -> real, sum: real)
    requires SumsTo(summands, sum)
    ensures Sum(summands) == sum
  {
    SumIsUnique(summands, Sum(summands), sum);
  }

  lemma RemoveFirstSummandFinite(summands: nat -> real, summands': nat -> real, start: nat, end: nat)
    decreases end - start
    requires forall n: nat :: summands(n + 1) == summands'(n)
    ensures SumFromTo(summands, start + 1, end + 1) == SumFromTo(summands', start, end)
  {
    if end <= start {} else {
      calc {
        SumFromTo(summands, start + 1, end + 1);
        summands(start + 1) + SumFromTo(summands, start + 2, end + 1);
        { RemoveFirstSummandFinite(summands, summands', start + 1, end); }
        summands'(start) + SumFromTo(summands', start + 1, end);
        SumFromTo(summands', start, end);
      }
    }
  }

  lemma RemoveLastSummand(summands: nat -> real, start: nat, end: nat)
    decreases end - start
    requires start < end
    ensures SumFromTo(summands, start, end) == SumFromTo(summands, start, end - 1) + summands(end - 1)
  {
    if start + 1 == end {} else {
      calc {
        SumFromTo(summands, start, end);
        summands(start) + SumFromTo(summands, start + 1, end);
        { RemoveLastSummand(summands, start + 1, end); }
        summands(start) + SumFromTo(summands, start + 1, end - 1) + summands(end - 1);
        SumFromTo(summands, start, end - 1) + summands(end - 1);
      }
    }
  }

  lemma RemoveFirstSummand(summands: nat -> real, summands': nat -> real, first: real, sum': real)
    requires first == summands(0)
    requires forall n: nat :: summands(n + 1) == summands'(n)
    ensures SumsTo(summands, first + sum') <==> SumsTo(summands', sum')
  {
    var partialSums' := PartialSums(summands');
    var firstPlusPartialSums' := Sequences.Add(Sequences.Constant(first), partialSums');
    var partialSums := PartialSums(summands);
    assert Sequences.IsSuffixOf(firstPlusPartialSums', partialSums, 1) by {
      forall n: nat ensures partialSums(n + 1) == firstPlusPartialSums'(n) {
        calc {
          partialSums(n + 1);
          SumTo(summands, n + 1);
          first + SumFromTo(summands, 1, n + 1);
          { RemoveFirstSummandFinite(summands, summands', 0, n); }
          first + SumTo(summands', n);
          first + partialSums'(n);
          firstPlusPartialSums'(n);
        }
      }
    }
    assert limitPlusFirst: Limits.ConvergesTo(firstPlusPartialSums', first + sum') <==> Limits.ConvergesTo(partialSums', sum') by {
      assert Limits.ConvergesTo(Sequences.Constant(first), first) by {
        Limits.ConstantSequenceConverges(Sequences.Constant(first), first);
      }
      if Limits.ConvergesTo(partialSums', sum') {
        Limits.LimitIsAdditive(Sequences.Constant(first), first, partialSums', sum');
      }
      if Limits.ConvergesTo(firstPlusPartialSums', first + sum') {
        var canceled := Sequences.Add(Sequences.Constant(-first), firstPlusPartialSums');
        assert Sequences.IsSuffixOf(canceled, partialSums', 0);
        Limits.ConstantSequenceConverges(Sequences.Constant(-first), -first);
        Limits.LimitIsAdditive(Sequences.Constant(-first), -first, firstPlusPartialSums', first + sum');
        Limits.SuffixConvergesToSame(partialSums', canceled, 0, sum');
      }
    }
    calc {
      SumsTo(summands, first + sum');
      Limits.ConvergesTo(partialSums, first + sum');
      { Limits.SuffixConvergesToSame(partialSums, firstPlusPartialSums', 1, first + sum'); }
      Limits.ConvergesTo(firstPlusPartialSums', first + sum');
      { reveal limitPlusFirst; }
      Limits.ConvergesTo(partialSums', sum');
      SumsTo(summands', sum');
    }
  }

  lemma PartialSumsZero(summands: nat -> real, end: nat, start: nat := 0)
    decreases end - start
    requires forall i: nat :: summands(i) == 0.0
    ensures SumFromTo(summands, start, end) == 0.0
  {
    if end <= start {} else {
      calc {
        SumFromTo(summands, start, end);
        SumFromTo(summands, start + 1, end);
        { PartialSumsZero(summands, end, start + 1); }
        0.0;
      }
    }
  }

  lemma ZeroSuffixSum(summands: nat -> real, prefix: nat, sum: real)
    requires PartialSums(summands)(prefix) == sum
    requires forall n: nat | n >= prefix :: summands(n) == 0.0
    ensures SumsTo(summands, sum)
  {
    if prefix == 0 {
      forall n: nat ensures PartialSums(summands)(n) == 0.0 {
        PartialSumsZero(summands, n);
      }
      Limits.ConstantSequenceConverges(PartialSums(summands), 0.0);
    } else {
      var rest := (n: nat) => summands(n + 1);
      var restSum := PartialSums(rest)(prefix - 1);
      assert restSum == sum - summands(0) by {
        calc {
          restSum;
          { RemoveFirstSummandFinite(summands, rest, 1, prefix - 1); }
          SumFromTo(summands, 1, prefix);
          sum - summands(0);
        }
      }
      assert SumsTo(rest, restSum) by {
        RemoveFirstSummandFinite(summands, rest, 0, prefix - 1);
        ZeroSuffixSum(rest, prefix - 1, restSum);
      }
      assert SumsTo(summands, sum) by {
        RemoveFirstSummand(summands, rest, summands(0), restSum);
      }
    }
  }
}

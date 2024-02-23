 module Series {
  import NatArith
  import RealArith
  import Limits

  ghost predicate SumsTo(summands: nat -> real, sum: real) {
    Limits.ConvergesTo(PartialSums(summands), sum)
  }

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

  ghost predicate IsSummable(summands: nat -> real) {
    exists sum: real :: SumsTo(summands, sum)
  }

  ghost function Sum(summands: nat -> real): real
    requires IsSummable(summands)
  {
    Limits.Limit(PartialSums(summands))
  }

}
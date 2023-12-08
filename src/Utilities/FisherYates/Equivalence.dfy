/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module FisherYates.Equivalence {
  import Model 
  import Rand
  import Monad
  import Uniform
  import Permutations
  import Loops

  lemma ShuffleLoopTailRecursiveEquivalence<T(!new)>(xs: seq<T>, s: Rand.Bitstream, i: nat := 0)
    requires 0 <= i <= |xs|
    ensures 
      Model.ShuffleLoop(xs)(s) ==
        if i < |xs| then
          Monad.Bind(
            Uniform.Model.IntervalSample(i, |xs|),
            (j: int) requires i <= j < |xs| => 
              var xs := Permutations.Swap(xs, 0, j);
              Model.ShuffleLoop(xs, i + 1)
          )(s)
        else 
          Monad.Return((xs, i))(s)
  {
    calc {
      Model.ShuffleLoop(xs, i)(s);
    == { reveal Model.ShuffleLoop(); 
         reveal Model.ShuffleWhileLoopCondition();
         reveal Model.ShuffleWhileLoopBody();
         reveal Loops.While(); }
      Loops.While(Model.ShuffleWhileLoopCondition, Model.ShuffleWhileLoopBody)((xs, i))(s);
    == { Model.ShuffleTerminatesAlmostSurely<T>();
         Loops.WhileUnroll(Model.ShuffleWhileLoopCondition, Model.ShuffleWhileLoopBody, (xs, i), s); 
         reveal Model.ShuffleWhileLoopCondition();
         reveal Model.ShuffleWhileLoopBody(); 
         reveal Model.ShuffleLoop(); }
      if Model.ShuffleWhileLoopCondition((xs, i)) then 
        Monad.Bind(
          Model.ShuffleWhileLoopBody((xs, i)),
          (xsI: (seq<T>, nat)) => Model.ShuffleLoop(xsI.0, xsI.1)
        )(s)
      else 
        Monad.Return((xs, i))(s);
    == { reveal Model.ShuffleWhileLoopBody(); 
         reveal Model.ShuffleWhileLoopCondition(); 
         reveal Model.ShuffleLoop(); }
      if i < |xs| then 
        var h: Monad.Hurd<(seq<T>, nat)> := 
          (if i < |xs| then 
            Monad.Bind(
              Uniform.Model.IntervalSample(i, |xs|),
              (j: int) requires i <= j < |xs| => 
                var xs := Permutations.Swap(xs, i, j); 
                Monad.Return((xs, i + 1))
            )
          else 
            Monad.Return((xs, i)));
        Monad.Bind(
          h,
          (xsI: (seq<T>, nat)) => Model.ShuffleLoop(xsI.0, xsI.1)
        )(s)
      else 
        Monad.Return((xs, i))(s);  
    ==
      if i < |xs| then 
        var h: Monad.Hurd<(seq<T>, nat)> := 
          Monad.Bind(
            Uniform.Model.IntervalSample(i, |xs|),
            (j: int) requires i <= j < |xs| => 
              var xs := Permutations.Swap(xs, i, j); 
              Monad.Return((xs, i + 1))
          );
        Monad.Bind(
          h,
          (xsI: (seq<T>, nat)) => Model.ShuffleLoop(xsI.0, xsI.1)
        )(s)
      else 
        Monad.Return((xs, i))(s);  
    ==
      if i < |xs| then 
        Monad.Bind(
          Uniform.Model.IntervalSample(i, |xs|),
          (j: int) requires i <= j < |xs| => 
            var xs := Permutations.Swap(xs, i, j); 
            var h: Monad.Hurd<(seq<T>, nat)> := Monad.Return((xs, i + 1));
            Monad.Bind(
              h,
              (xsI: (seq<T>, nat)) => Model.ShuffleLoop(xsI.0, xsI.1)
            )
          )(s)
      else 
        Monad.Return((xs, i))(s);
    == { forall xsI: (seq<T>, nat), s: Rand.Bitstream { Monad.UnitalityBindReturn(xsI, (xsI: (seq<T>, nat)) => Model.ShuffleLoop(xsI.0, xsI.1), s); } }
      if i < |xs| then
        Monad.Bind(
          Uniform.Model.IntervalSample(i, |xs|),
          (j: int) requires i <= j < |xs| => 
            var xs := Permutations.Swap(xs, i, j);
            Model.ShuffleLoop(xs, i + 1)
        )(s)
      else 
        Monad.Return((xs, i))(s);
    }
  }


  lemma ShuffleLiftToEnsures<T(!new)>(s: Rand.Bitstream, t: Rand.Bitstream, xs: seq<T>, ys: seq<T>, i: nat)
    requires R1: Model.ShuffleLoop(xs)(s) == Model.ShuffleLoop(ys, i)(t)
    requires R2: !(i < |ys|)
    ensures Model.Shuffle(xs)(s) == Monad.Result(ys, t)
  {
    var f := (xsI: (seq<T>, nat)) => xsI.0;

    calc {
      Model.Shuffle(xs)(s);
      { reveal Model.Shuffle(); }
      Monad.Map(Model.ShuffleLoop(xs), f)(s);
      Model.ShuffleLoop(xs)(s).Map(f);
      { reveal R1; }
      Model.ShuffleLoop(ys, i)(t).Map(f);
      { reveal Model.ShuffleLoop(); 
        reveal Model.ShuffleWhileLoopCondition(); 
        reveal Model.ShuffleWhileLoopBody(); }
      Loops.While(Model.ShuffleWhileLoopCondition, Model.ShuffleWhileLoopBody)((ys, i))(t).Map(f);
      { reveal Loops.While(); 
        reveal Model.ShuffleWhileLoopCondition(); 
        reveal Model.ShuffleWhileLoopBody(); 
        reveal R2; }
      Monad.Return((ys, i))(t).Map(f);
      Monad.Result((ys, i), t).Map(f);
      Monad.Result(f((ys, i)), t);
      Monad.Result(ys, t);
    }
  }
}
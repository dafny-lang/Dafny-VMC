/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module FisherYates.Model {
  import Monad
  import Rand
  import Permutations
  import Uniform
  import Loops

  /************
   Definitions
  ************/
  
  opaque ghost function Shuffle<T(!new)>(xs: seq<T>): (f: Monad.Hurd<seq<T>>) {
    var f := (xsI: (seq<T>, nat)) => xsI.0;
    Monad.Map(ShuffleLoop(xs), f)
  }

  opaque ghost function ShuffleLoop<T(!new)>(xs: seq<T>, i: nat := 0): (f: Monad.Hurd<(seq<T>, nat)>) 
  {
    Loops.While(ShuffleWhileLoopCondition, ShuffleWhileLoopBody)((xs, i))
  }

  opaque function ShuffleWhileLoopCondition<T>(xsI: (seq<T>, nat)): bool {
    xsI.1 < |xsI.0|
  }

  opaque ghost function ShuffleWhileLoopBody<T>(xsI: (seq<T>, nat)): Monad.Hurd<(seq<T>, nat)> {
    if xsI.1 < |xsI.0| then
      Monad.Bind(
        Uniform.Model.IntervalSample(xsI.1, |xsI.0|), 
        (j: int) requires xsI.1 <= j < |xsI.0| => 
          Monad.Return((Permutations.Swap(xsI.0, xsI.1, j), xsI.1 + 1))
      )
    else 
      Monad.Return(xsI)
  }

  /*******
   Lemmas
  *******/

  lemma {:axiom} ShuffleTerminatesAlmostSurely<T>()
    ensures Loops.WhileTerminatesAlmostSurely<(seq<T>, nat)>(ShuffleWhileLoopCondition, ShuffleWhileLoopBody)

}
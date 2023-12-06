/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module FisherYates.Interface {
  import Uniform
  import Model

  trait {:termination false} Trait extends Uniform.Interface.Trait {

    method Shuffle<T>(a: array<T>)
      modifies this, a
      decreases *
    //    ensures Model.Shuffle(Helper.ArrayToSeq(old(a)))(old(s)) == Monad.Result(Helper.ArrayToSeq(a), s)

  }
}
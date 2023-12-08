/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module FisherYates.Interface {
  import Uniform
  import Model
  import Helper
  import Monad

  trait {:termination false} Trait extends Uniform.Interface.Trait {

    method Shuffle<T(!new)>(a: array<T>)
      modifies this, a
      decreases *
      ensures Model.Shuffle(old(Helper.ArrayToSeq(a)))(old(s)) == Monad.Result(Helper.ArrayToSeq(a), s)

  }
}
/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module FisherYates.Interface {
  import Uniform
  import Model

  trait {:termination false} Trait extends Uniform.Interface.Trait {

    method Shuffle<T>(a: array<T>) returns (b: array<T>)
      modifies this
      decreases *
//    ensures Model.Shuffle(Helper.ArrayToSeq(a))(old(s)) == Monad.Result(Helper.ArrayToSeq(b), s)

  }
 }
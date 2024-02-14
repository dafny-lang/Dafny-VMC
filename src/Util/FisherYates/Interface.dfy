/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module FisherYates.Interface {
  import Uniform
  import Model
  import Monad

  trait {:termination false} Trait extends Uniform.Interface.Trait {

    method Shuffle<T>(a: array<T>, t: Uniform.Interface.Trait := this)
      decreases *
      modifies `s, a
      ensures Model.Shuffle(old(a[..]))(old(s)) == Monad.Result(a[..], s)

  }
}
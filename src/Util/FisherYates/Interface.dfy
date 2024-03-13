/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module FisherYates.Interface {
  import Uniform
  import Model
  import Monad

  trait {:termination false} Trait extends Uniform.Interface.Trait32 {

    method Shuffle<T>(a: array<T>)
      decreases *
      modifies `s, a
      requires a.Length < 0x8000_0000
      ensures Model.Shuffle(old(a[..]))(old(s)) == Monad.Result(a[..], s)

  }
}
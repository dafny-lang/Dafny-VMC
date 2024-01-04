/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module FisherYates.Interface {
  import Uniform

  trait {:termination false} Trait extends Uniform.Interface.Trait {

    method Shuffle<T(!new)>(a: array<T>)
      decreases *
      modifies this, a

  }
}
/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module FisherYates.Interface {
  import Uniform

  trait {:termination false} Trait extends Uniform.Interface.Trait {

    method Shuffle<T>(a: array<T>)
      decreases *
      modifies this, a

    method ShuffleBigInteger(a: array<int>)
      decreases *
      modifies this, a
    {
      Shuffle<int>(a);
    }

    method ShuffleBool(a: array<bool>)
      decreases *
      modifies this, a
    {
      Shuffle<bool>(a);
    }
  }
}
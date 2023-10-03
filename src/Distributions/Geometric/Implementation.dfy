/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

include "../../ProbabilisticProgramming/Monad.dfy"
include "Interface.dfy"
include "Model.dfy"

module GeometricImplementation {
  import Interface = GeometricInterface
  import Monad
  import Model = GeometricModel

  trait {:termination false} Trait extends Interface.Trait {

    method GeometricSample() returns (c: nat)
      modifies this
      decreases *
      ensures Model.Sample()(old(s)) == (c, s)
    {
      assume {:axiom} false;
      c := 0;
      var b := CoinSample();
      while b
        decreases *
      {
        b := CoinSample();
        c := c + 1;
      }
    }

  }
}
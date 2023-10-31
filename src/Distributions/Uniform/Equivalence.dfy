/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module Uniform.Equivalence {
  import Rand
  import Model
  import Monad

  lemma SampleUnroll(n: nat, s: Rand.Bitstream)
    requires n > 0
    ensures Model.Sample(n)(s) == Monad.Bind(Model.Proposal(n), (x: nat) => if Model.Accept(n)(x) then Monad.Return(x) else Model.Sample(n))(s)
  {
    //Model.SampleTerminates(n);
    reveal Model.Sample();
    Monad.UntilUnroll(Model.Proposal(n), Model.Accept(n), s);
  }
}

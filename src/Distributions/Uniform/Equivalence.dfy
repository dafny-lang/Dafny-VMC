/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module Uniform.Equivalence {
  import Rand
  import Model
  import Monad
  import Loops

  lemma SampleUnroll(n: nat, s: Rand.Bitstream)
    requires n > 0
    ensures Model.Sample(n)(s) == Monad.Bind(Model.Proposal(n), (x: nat) => if Model.Accept(n)(x) then Monad.Return(x) else Model.Sample(n))(s)
  {
    Model.SampleTerminates(n);
    reveal Model.Sample();
    Loops.UntilUnroll(Model.Proposal(n), Model.Accept(n), s);
  }

  lemma SampleLifts(n: nat, u: nat, oldS: Rand.Bitstream, prevS: Rand.Bitstream, s: Rand.Bitstream)
    requires n > 0
    requires Model.Sample(n)(oldS) == Model.Sample(n)(prevS)
    requires Monad.Result(u, s) == Model.Proposal(n)(prevS)
    requires Model.Accept(n)(u)
    ensures Model.Sample(n)(oldS) == Monad.Result(u, s)
  {
    reveal Model.Sample();
    Model.SampleTerminates(n);
    Loops.UntilUnroll(Model.Proposal(n), Model.Accept(n), prevS);
  }
}

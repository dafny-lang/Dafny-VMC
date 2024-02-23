/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module {:extern} DafnyVMCPartMaterial {
  class {:extern} Random {
    // For running Dafny native testing with standard SecureRandom rng
    static method {:extern "UniformSample"} ExternUniformSample(n: nat) returns (u: nat)
  }
}

module {:extern "DafnyVMCPart"} DafnyVMC {
  import DafnyVMCTrait
  import DafnyVMCPartMaterial
  import Monad
  import Uniform
  import Pos

  class Random extends DafnyVMCTrait.RandomTrait {
    constructor {:extern} ()

    method UniformSample(n: Pos.pos) returns (u: nat)
      modifies `s
      decreases *
      ensures u < n
      ensures Uniform.Model.Sample(n)(old(s)) == Monad.Result(u, s)
    {
      u := DafnyVMCPartMaterial.Random.ExternUniformSample(n);
      assume {:axiom} false; // assume correctness of extern implementation
    }
  }

}
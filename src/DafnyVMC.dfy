/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module {:extern} DafnyVMCPartMaterial {
  import opened Pos

  class {:extern} Random {
    // For running Dafny native testing with standard SecureRandom rng
    static method {:extern "UniformPowerOfTwoSample"} ExternUniformPowerOfTwoSample(n: nat) returns (u: nat)

    static method {:extern "UniformSample32"} ExternUniformSample32(n: pos32) returns (u: nat32)
  }
}

module {:extern "DafnyVMCPart"} DafnyVMC {
  import DafnyVMCTrait
  import DafnyVMCPartMaterial
  import Monad
  import UniformPowerOfTwo
  import Uniform
  import opened Pos

  class Random extends DafnyVMCTrait.RandomTrait {
    constructor {:extern} ()

    method UniformPowerOfTwoSample(n: nat) returns (u: nat)
      requires n >= 1
      modifies `s
    {
      u := DafnyVMCPartMaterial.Random.ExternUniformPowerOfTwoSample(n);
    }

    method {:verify false} UniformSample32(n: pos32) returns (u: nat32)
      modifies `s
      decreases *
      ensures u < n
      ensures Uniform.Model.Sample(n as nat)(old(s)) == Monad.Result(u as nat, s)
    {
      u := DafnyVMCPartMaterial.Random.ExternUniformSample32(n);
    }
  }

}
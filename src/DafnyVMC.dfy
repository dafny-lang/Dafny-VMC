/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module {:extern} DafnyVMCPartMaterial {
  class {:extern} Random {
    // For running Dafny native testing with standard SecureRandom rng
    static method {:extern "UniformPowerOfTwoSample"} ExternUniformPowerOfTwoSample(n: nat) returns (u: nat)
  }
}

module {:extern "DafnyVMCPart"} DafnyVMC {
  import DafnyVMCTrait
  import DafnyVMCPartMaterial
  import Monad
  import UniformPowerOfTwo

  class Random extends DafnyVMCTrait.RandomTrait {
    constructor {:extern} ()

    method UniformPowerOfTwoSample(n: nat) returns (u: nat)
      requires n >= 1
      modifies `s
    {
      u := DafnyVMCPartMaterial.Random.ExternUniformPowerOfTwoSample(n);
    }
  }

}
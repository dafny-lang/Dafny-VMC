/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module {:extern "DafnyVMCPart"} DafnyVMC {
  import NewVMCTrait
  import Monad
  import UniformPowerOfTwo

  // For running Dafny native testing with standard SecureRandom rng
  method {:extern "DafnyVMCPartMaterial.Random", "UniformPowerOfTwoSample"} ExternUniformPowerOfTwoSample(n: nat) returns (u: nat)

  class Random extends NewVMCTrait.RandomTrait {
    constructor {:extern} ()

    method UniformPowerOfTwoSample(n: nat) returns (u: nat)
      requires n >= 1
      modifies this
      ensures UniformPowerOfTwo.Model.Sample(n)(old(s)) == Monad.Result(u, s)
    {
      u := ExternUniformPowerOfTwoSample(n);
      assume {:axiom} false; // assume correctness of extern implementation
    }
  }

}
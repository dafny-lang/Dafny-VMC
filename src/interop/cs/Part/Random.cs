using System;
using System.Threading;
using System.Numerics;

namespace DafnyVMCPartMaterial {

  public sealed class Random {

    private static readonly ThreadLocal<System.Random> RNG = new ThreadLocal<System.Random>(createRandom);
    
    private Random() {} // Prevent instantiation

    private static System.Random createRandom() {
      var rng = new System.Random();
      // Required for proper initialization
      rng.Next(2); 
      return rng;
    }

    // Let k be such that 2^k <= n < 2^(k+1). Then the model UniformPowerOfTwo(n) returns a uniform random value in {0, ..., 2^k - 1}.
    // E.g. for n = 8, the model returns a uniform random value in {0, ..., 7 = 2^3 - 1}.
    public static BigInteger UniformPowerOfTwoSample(BigInteger n) {
      if (n.Sign < 1) {
        throw new ArgumentException("n must be positive");
      }

      // Constructs a uniform random BigInteger in {0, ..., 2^k - 1)}, where k == n.GetBitLength() - 1.
      // E.g. for n = 8, we have k=3, since 2^{3} <= n < 2^{3+1}, and k == 3 == 4 - 1 = n.GetBitLength() - 1, as desired.
      // Next(m) returns a uniform random value in {0, ..., m - 1}.
      var m = (long) Math.Pow(2, n.GetBitLength() - 1); // converting double to long
      var o = RNG.Value.NextInt64(m);
      return new BigInteger(o);
    }
  }

}
package DafnyVMCPartMaterial;

import java.security.SecureRandom;
import java.math.BigInteger;
import java.lang.Thread;

public final class Random {

  private static final ThreadLocal<SecureRandom> RNG = ThreadLocal.withInitial(Random::createSecureRandom);
  
  private Random() {} // Prevent instantiation

  private static final SecureRandom createSecureRandom() {
    final SecureRandom rng = new SecureRandom();
    // Required for proper initialization
    rng.nextBoolean(); 
    return rng;
  }

  // Let k be such that 2^k <= n < 2^(k+1). Then the model UniformPowerOfTwo(n) returns a uniform random value in {0, ..., 2^k - 1}.
  // E.g. for n = 8, the model returns a uniform random value in {0, ..., 7 = 2^3 - 1}.
  public static BigInteger UniformPowerOfTwoSample(BigInteger n) {
    if (n.compareTo(BigInteger.ONE) < 0) {
      throw new IllegalArgumentException("n must be positive");
    }

    // BigInteger(int numBits, Random rnd) constructs a randomly generated BigInteger, uniformly distributed over the range 0 to (2^numBits - 1), inclusive.
    // For n = 8, we have 2^3 <= 8 < 2^{3+1}, i.e. k == 3 = 4 - 1 == n.bitLength() - 1
    // We thus return a uniform random value in {0, ..., 2^{n.bitLength()-1} - 1 == 2^k - 1}, as desired.
    return new BigInteger(n.bitLength()-1, RNG.get());
  }
}
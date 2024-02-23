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

  public static BigInteger UniformPowerOfTwoSample(BigInteger n) {
    if (n.compareTo(BigInteger.ONE) < 0) {
      throw new IllegalArgumentException("n must be positive");
    }

    return new BigInteger(n.bitLength()-1, RNG.get());
  }

  public static BigInteger UniformSample(BigInteger n) {
    if (n.compareTo(BigInteger.ONE) < 0) {
      throw new IllegalArgumentException("n must be positive");
    }

    BigInteger sampleValue;

    do {
      sampleValue = UniformPowerOfTwoSample(n);
    } while (sampleValue.compareTo(n) >= 0);

    return sampleValue;    
  }
}
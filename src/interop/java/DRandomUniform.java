package Uniform_mImplementation;

import java.security.SecureRandom;
import java.math.BigInteger;
import java.lang.Thread;

public final class DRandomUniform {
  private static final ThreadLocal<SecureRandom> RNG = ThreadLocal.withInitial(DRandomUniform::createSecureRandom);
  private DRandomUniform() {} // Prevent instantiation

  private static final SecureRandom createSecureRandom() {
    final SecureRandom rng = new SecureRandom();
    // Required for proper initialization
    rng.nextBoolean(); 
    return rng;
  }

  /**
   * Sample a uniform value using rejection sampling between [0, n).
   * 
   * @param n an integer (must be >= 1)
   * @return a uniform value between 0 and n-1
   * @throws IllegalArgumentException if `n` is less than 1
   */
  public static BigInteger Uniform(final BigInteger n) {
    if (n.compareTo(BigInteger.ONE) < 0) {
      throw new IllegalArgumentException("n must be positive");
    }

    BigInteger sampleValue;
    do {
      sampleValue = new BigInteger(n.bitLength(), RNG.get());
    } while (sampleValue.compareTo(n) >= 0);

    return sampleValue;
  }
}
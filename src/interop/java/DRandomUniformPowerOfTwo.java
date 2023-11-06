package UniformPowerOfTwo_mImplementation;

import java.security.SecureRandom;
import java.math.BigInteger;
import java.lang.Thread;

public final class DRandomUniformPowerOfTwo {

  private static final ThreadLocal<SecureRandom> RNG = ThreadLocal.withInitial(DRandomUniformPowerOfTwo::createSecureRandom);
  
  private DRandomUniformPowerOfTwo() {} // Prevent instantiation

  private static final SecureRandom   createSecureRandom() {
    final SecureRandom rng = new SecureRandom();
    // Required for proper initialization
    rng.nextBoolean(); 
    return rng;
  }

  public static BigInteger UniformPowerOfTwo(BigInteger n) {
    if (n.compareTo(BigInteger.ONE) < 0) {
      throw new IllegalArgumentException("n must be positive");
    }

    return new BigInteger(n.bitLength(), RNG.get());
  }
}
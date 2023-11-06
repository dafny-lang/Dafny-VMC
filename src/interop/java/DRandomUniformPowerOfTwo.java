package Uniform_mImplementation;

import java.security.SecureRandom;
import java.math.BigInteger;
import java.lang.Thread;

public final class DRandomUniformPowerOfTwo {

  private static final ThreadLocal<SecureRandom> RNG = ThreadLocal.withInitial(DRandomUniform::createSecureRandom);
  
  private DRandomUniformPowerOfTwo() {} // Prevent instantiation

  private static final SecureRandom createSecureRandom() {
    final SecureRandom rng = new SecureRandom();
    // Required for proper initialization
    rng.nextBoolean(); 
    return rng;
  }

  public static BigInteger Uniform(BigInteger n) {
    // `n.intValueExact` will throw an `ArithmeticException` if `n` does not fit in an `int`.
    // see https://docs.oracle.com/javase/8/docs/api/java/math/BigInteger.html#intValueExact--
    return BigInteger.valueOf(RNG.get().nextInt(n.intValueExact()));
  }
}

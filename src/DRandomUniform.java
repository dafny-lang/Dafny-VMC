package UniformImplementation;

import java.security.SecureRandom;
import java.math.BigInteger;

public class DRandomUniform {
  private static SecureRandom r = new SecureRandom();

  public static BigInteger Uniform(BigInteger n) {
    // `longValueExact` will throw an exception if `n` does not fit in a `long`.
    // see https://docs.oracle.com/javase/8/docs/api/java/math/BigInteger.html#longValueExact--
    return BigInteger.valueOf(r.nextLong(n.longValueExact()));
  }
}

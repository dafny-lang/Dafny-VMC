package Uniform.Implementation;

import java.security.SecureRandom;
import java.math.BigInteger;

public class DRandomUniform {
  private static SecureRandom r = new SecureRandom();

  public static BigInteger Uniform(BigInteger n) {
    // `intValueExact` will throw an `ArithmeticException` if `n` does not fit in an `int`.
    // see https://docs.oracle.com/javase/8/docs/api/java/math/BigInteger.html#intValueExact--
    return BigInteger.valueOf(r.nextInt(n.intValueExact()));
  }
}

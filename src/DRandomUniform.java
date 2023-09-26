package UniformImplementation;

import java.security.SecureRandom;
import java.math.BigInteger;

public class DRandomUniform {
  private static SecureRandom r = new SecureRandom();

  public static BigInteger Uniform(BigInteger n) {
    return BigInteger.valueOf(r.nextInt(n.intValue()));
  }
}
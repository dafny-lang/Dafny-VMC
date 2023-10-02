package CoinImplementation;

import java.security.SecureRandom;
import java.math.BigInteger;

public class DRandomCoin {
  private static SecureRandom r = new SecureRandom();

  public static boolean CoinSample() {
    return r.nextBoolean();
  }
}
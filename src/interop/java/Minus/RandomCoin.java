package Extern;

import java.security.SecureRandom;
import java.math.BigInteger;
import java.lang.Thread;

public final class RandomCoin {

  private static final ThreadLocal<SecureRandom> RNG = ThreadLocal.withInitial(RandomCoin::createSecureRandom);

  private RandomCoin() {} // Prevent instantiation

  private static final SecureRandom createSecureRandom() {
    final SecureRandom rng = new SecureRandom();
    // Required for proper initialization
    rng.nextBoolean(); 
    return rng;
  }

  public static boolean Coin() {
    return RNG.get().nextBoolean();
  }

}
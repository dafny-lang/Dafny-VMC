package DafnyVMC;

import dafny.TypeDescriptor;
import java.math.BigInteger;
import java.security.SecureRandom;

public class Random implements DafnyVMCMinus.Random {
  static ThreadLocal<SecureRandom> rng;
  
  public Random() {
    this.rng = ThreadLocal.withInitial(Random::createSecureRandom);
  }

  public Random(SecureRandom rng) {
    this.rng = ThreadLocal.withInitial(() -> rng);
  }

  private static final SecureRandom createSecureRandom() {
    final SecureRandom rng = new SecureRandom();
    // Required for proper initialization
    rng.nextBoolean(); 
    return rng;
  }

  public BigInteger UniformPowerOfTwo(BigInteger n) {
    if (n.compareTo(BigInteger.ONE) < 0) {
      throw new IllegalArgumentException("n must be positive");
    }

    return new BigInteger(n.bitLength()-1, rng.get());
  }

  public void Shuffle2(BigInteger[] arr) {
    FisherYates.Implementation._Companion_Trait.Shuffle(TypeDescriptor.BIG_INTEGER, this, arr);
  }

  public void Shuffle2(int[] arr) {
    Shuffle(TypeDescriptor.INT, arr);
  }

  public void Shuffle2(String[] arr) {
    Shuffle(TypeDescriptor.CHAR_ARRAY, arr);
  }

  public void Shuffle2(char[] arr) {
    Shuffle(TypeDescriptor.CHAR, arr);
  }

  public void Shuffle2(boolean[] arr) {
    Shuffle(TypeDescriptor.BOOLEAN, arr);
  }

  public void Shuffle2(long[] arr) {
    Shuffle(TypeDescriptor.LONG, arr);
  }

  public void Shuffle2(short[] arr) {
    Shuffle(TypeDescriptor.SHORT, arr);
  }
}
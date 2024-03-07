package DafnyVMC;

import dafny.TypeDescriptor;
import java.math.BigInteger;
import java.security.SecureRandom;
import java.util.function.Supplier;

public class CustomRandom extends Random {
  public CustomRandom() {
    this.rng = ThreadLocal.withInitial(CustomRandom::createSecureRandom);
  }

  public CustomRandom(Supplier<SecureRandom> supplier) {
    this.rng = ThreadLocal.withInitial(supplier);
  }

  private static final SecureRandom createSecureRandom() {
    final SecureRandom rng = new SecureRandom();
    // Required for proper initialization
    rng.nextBoolean(); 
    return rng;
  }
  
  @Override
  public java.math.BigInteger UniformSample(java.math.BigInteger n) {
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
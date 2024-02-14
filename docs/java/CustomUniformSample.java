import Uniform.Interface.TraitMinus;
import Uniform.Interface.Trait;
import java.math.BigInteger;
import java.security.SecureRandom;
import java.util.Random;

class CustomUniformSampleMinus implements Uniform.Interface.TraitMinus {
  static ThreadLocal<SecureRandom> rng;

  public CustomUniformSampleMinus() {
      CustomUniformSampleMinus.rng = ThreadLocal.withInitial(CustomUniformSampleMinus::createSecureRandom);
  }

  private static final SecureRandom createSecureRandom() {
      final SecureRandom rng = new SecureRandom();
      // Required for proper initialization
      rng.nextBoolean(); 
      return rng;
  }

  public BigInteger UniformPowerOfTwoSample(BigInteger n) {
      if (n.compareTo(BigInteger.ONE) < 0) {
        throw new IllegalArgumentException("n must be positive");
      }
  
      return new BigInteger(n.bitLength()-1, rng.get());
  }
  
  public BigInteger UniformSample(BigInteger n) {
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

public class CustomUniformSample extends CustomUniformSampleMinus implements Uniform.Interface.Trait {
  public java.math.BigInteger UniformIntervalSample(java.math.BigInteger a, java.math.BigInteger b) {
    return Uniform.Interface._Companion_Trait.UniformIntervalSample(this, a, b);
  }
}
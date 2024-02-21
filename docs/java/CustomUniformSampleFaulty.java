import Uniform.Interface.TraitMinus;
import Uniform.Interface.Trait;
import java.math.BigInteger;
import java.security.SecureRandom;
import java.util.Random;

class CustomUniformSampleFaultyMinus implements Uniform.Interface.TraitMinus {
  static ThreadLocal<SecureRandom> rng;

  public CustomUniformSampleFaultyMinus() {
      CustomUniformSampleFaultyMinus.rng = ThreadLocal.withInitial(CustomUniformSampleFaultyMinus::createSecureRandom);
  }

  private static final SecureRandom createSecureRandom() {
      final SecureRandom rng = new SecureRandom();
      // Required for proper initialization
      rng.nextBoolean(); 
      return rng;
  }
  
  public BigInteger UniformSample(BigInteger n) {
    return BigInteger.valueOf(0); // Faulty; only for demonstration purposes
  }
}

public class CustomUniformSampleFaulty extends CustomUniformSampleFaultyMinus implements Uniform.Interface.Trait {
  public java.math.BigInteger UniformIntervalSample(java.math.BigInteger a, java.math.BigInteger b) {
    return Uniform.Interface._Companion_Trait.UniformIntervalSample(this, a, b);
  }
}
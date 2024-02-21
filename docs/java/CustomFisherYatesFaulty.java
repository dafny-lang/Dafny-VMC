import Uniform.Interface.TraitMinus;
import Uniform.Interface.Trait;
import java.math.BigInteger;
import java.security.SecureRandom;
import java.util.Random;
import dafny.TypeDescriptor;

class CustomUniformSampleFaultyMinus implements Uniform.Interface.TraitMinus {  
  public BigInteger UniformSample(BigInteger n) {
    return BigInteger.valueOf(0);
  }
}

class CustomUniformFaulty extends CustomUniformSampleFaultyMinus implements Uniform.Interface.Trait {
  public java.math.BigInteger UniformIntervalSample(java.math.BigInteger a, java.math.BigInteger b) {
    return Uniform.Interface._Companion_Trait.UniformIntervalSample(this, a, b);
  }
}

class CustomFisherYatesMinusFaulty extends CustomUniformFaulty implements FisherYates.Implementation.Trait {
  public <__T> void Shuffle(dafny.TypeDescriptor<__T> _td___T, java.lang.Object a) {
    FisherYates.Implementation._Companion_Trait.Shuffle(_td___T, this, a);
  }

  public <__T> void Swap(dafny.TypeDescriptor<__T> _td___T, java.lang.Object a, java.math.BigInteger i, java.math.BigInteger j) {
    FisherYates.Implementation._Companion_Trait.Swap(_td___T, this, a, i, j);
  }
}

public class CustomFisherYatesFaulty extends CustomFisherYatesMinusFaulty {
  public void Shuffle(BigInteger[] arr) {
    this.Shuffle(TypeDescriptor.BIG_INTEGER, arr);
  }

  public void Shuffle(int[] arr) {
    this.Shuffle(TypeDescriptor.INT, arr);
  }

  public void Shuffle(String[] arr) {
    this.Shuffle(TypeDescriptor.CHAR_ARRAY, arr);
  }

  public void Shuffle(char[] arr) {
    this.Shuffle(TypeDescriptor.CHAR, arr);
  }

  public void Shuffle(boolean[] arr) {
    this.Shuffle(TypeDescriptor.BOOLEAN, arr);
  }

  public void Shuffle(long[] arr) {
    this.Shuffle(TypeDescriptor.LONG, arr);
  }

  public void Shuffle(short[] arr) {
    this.Shuffle(TypeDescriptor.SHORT, arr);
  }
}

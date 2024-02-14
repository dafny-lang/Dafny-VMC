package DafnyVMC;

import dafny.TypeDescriptor;
import java.math.BigInteger;
import java.security.SecureRandom;
import java.util.function.Supplier;

public class Random implements DafnyVMCTrait.RandomTrait {
  static ThreadLocal<SecureRandom> rng;
  
  public Random() {
    this.rng = ThreadLocal.withInitial(Random::createSecureRandom);
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

  public java.math.BigInteger UniformIntervalSample(java.math.BigInteger a, java.math.BigInteger b) {
    return Uniform.Interface._Companion_Trait.UniformIntervalSample(this, a, b);
  }

  public java.math.BigInteger UniformSample(java.math.BigInteger n) {
    return DafnyVMCTrait._Companion_RandomTrait.UniformSample(this, n);
  }

  public boolean BernoulliSample(java.math.BigInteger num, java.math.BigInteger den) {
    return DafnyVMCTrait._Companion_RandomTrait.BernoulliSample(this, num, den);
  }  

  public dafny.Tuple2<Boolean, java.math.BigInteger> BernoulliExpNegSampleUnitLoop(java.math.BigInteger num, java.math.BigInteger den, dafny.Tuple2<Boolean, java.math.BigInteger> state) {
    return DafnyVMCTrait._Companion_RandomTrait.BernoulliExpNegSampleUnitLoop(this, num, den, state);
  }

  public java.math.BigInteger BernoulliExpNegSampleUnitAux(java.math.BigInteger num, java.math.BigInteger den) {
    return DafnyVMCTrait._Companion_RandomTrait.BernoulliExpNegSampleUnitAux(this, num, den);
  }


  public boolean BernoulliExpNegSampleUnit(java.math.BigInteger num, java.math.BigInteger den) {
    return DafnyVMCTrait._Companion_RandomTrait.BernoulliExpNegSampleUnit(this, num, den);
  }


  public boolean BernoulliExpNegSampleGenLoop(java.math.BigInteger iter) {
    return DafnyVMCTrait._Companion_RandomTrait.BernoulliExpNegSampleGenLoop(this, iter);
  }


  public boolean BernoulliExpNegSample(java.math.BigInteger num, java.math.BigInteger den) {
    return DafnyVMCTrait._Companion_RandomTrait.BernoulliExpNegSample(this, num, den);
  }

  public dafny.Tuple2<java.math.BigInteger, Boolean> DiscreteGaussianSampleLoop(java.math.BigInteger num, java.math.BigInteger den, java.math.BigInteger t) {
    return DafnyVMCTrait._Companion_RandomTrait.DiscreteGaussianSampleLoop(this, num, den, t);
  }


  public java.math.BigInteger DiscreteGaussianSample(java.math.BigInteger num, java.math.BigInteger den) {
    return DafnyVMCTrait._Companion_RandomTrait.DiscreteGaussianSample(this, num, den);
  }

  public dafny.Tuple2<java.math.BigInteger, Boolean> DiscreteLaplaceSampleLoopIn1Aux(java.math.BigInteger t) {
    return DafnyVMCTrait._Companion_RandomTrait.DiscreteLaplaceSampleLoopIn1Aux(this ,t);
  }

  public java.math.BigInteger DiscreteLaplaceSampleLoopIn1(java.math.BigInteger t) {
    return DafnyVMCTrait._Companion_RandomTrait.DiscreteLaplaceSampleLoopIn1(this, t);
  }

  public dafny.Tuple2<Boolean, java.math.BigInteger> DiscreteLaplaceSampleLoopIn2Aux(java.math.BigInteger num, java.math.BigInteger den, dafny.Tuple2<Boolean, java.math.BigInteger> K) {
    return DafnyVMCTrait._Companion_RandomTrait.DiscreteLaplaceSampleLoopIn2Aux(this, num, den, K);
  }

  public java.math.BigInteger DiscreteLaplaceSampleLoopIn2(java.math.BigInteger num, java.math.BigInteger den) {
    return DafnyVMCTrait._Companion_RandomTrait.DiscreteLaplaceSampleLoopIn2(this, num, den);
  }

  public dafny.Tuple2<Boolean, java.math.BigInteger> DiscreteLaplaceSampleLoop(java.math.BigInteger num, java.math.BigInteger den) {
    return DafnyVMCTrait._Companion_RandomTrait.DiscreteLaplaceSampleLoop(this, num, den);
  }

  public java.math.BigInteger DiscreteLaplaceSample(java.math.BigInteger num, java.math.BigInteger den) {
    return DafnyVMCTrait._Companion_RandomTrait.DiscreteLaplaceSample(this, num, den);
  }

  public <__T> void Shuffle(dafny.TypeDescriptor<__T> _td___T, java.lang.Object a, Uniform.Interface.Trait t) {
    FisherYates.Implementation._Companion_Trait.Shuffle(_td___T, this, a, t);
  }

  public void Shuffle(BigInteger[] arr) {
    FisherYates.Implementation._Companion_Trait.Shuffle(TypeDescriptor.BIG_INTEGER, this, arr, this);
  }

  public void Shuffle(BigInteger[] arr, Uniform.Interface.Trait t) {
    FisherYates.Implementation._Companion_Trait.Shuffle(TypeDescriptor.BIG_INTEGER, this, arr, t);
  }

  public void Shuffle(int[] arr) {
    FisherYates.Implementation._Companion_Trait.Shuffle(TypeDescriptor.INT, this, arr, this);
  }

  public void Shuffle(int[] arr, Uniform.Interface.Trait t) {
    FisherYates.Implementation._Companion_Trait.Shuffle(TypeDescriptor.INT, this, arr, t);
  }

  public void Shuffle(String[] arr) {
    FisherYates.Implementation._Companion_Trait.Shuffle(TypeDescriptor.CHAR_ARRAY, this, arr, this);
  }

  public void Shuffle(String[] arr, Uniform.Interface.Trait t) {
    FisherYates.Implementation._Companion_Trait.Shuffle(TypeDescriptor.CHAR_ARRAY, this, arr, t);
  }

  public void Shuffle(char[] arr) {
    FisherYates.Implementation._Companion_Trait.Shuffle(TypeDescriptor.CHAR, this, arr, this);
  }

  public void Shuffle(char[] arr, Uniform.Interface.Trait t) {
    FisherYates.Implementation._Companion_Trait.Shuffle(TypeDescriptor.CHAR, this, arr, t);
  }

  public void Shuffle(boolean[] arr) {
    FisherYates.Implementation._Companion_Trait.Shuffle(TypeDescriptor.BOOLEAN, this, arr, this);
  }

  public void Shuffle(boolean[] arr, Uniform.Interface.Trait t) {
    FisherYates.Implementation._Companion_Trait.Shuffle(TypeDescriptor.BOOLEAN, this, arr, t);
  }

  public void Shuffle(long[] arr) {
    FisherYates.Implementation._Companion_Trait.Shuffle(TypeDescriptor.LONG, this, arr, this);
  }

  public void Shuffle(long[] arr, Uniform.Interface.Trait t) {
    FisherYates.Implementation._Companion_Trait.Shuffle(TypeDescriptor.LONG, this, arr, t);
  }

  public void Shuffle(short[] arr) {
    FisherYates.Implementation._Companion_Trait.Shuffle(TypeDescriptor.SHORT, this, arr, this);
  }

  public void Shuffle(short[] arr, Uniform.Interface.Trait t) {
    FisherYates.Implementation._Companion_Trait.Shuffle(TypeDescriptor.SHORT, this, arr, t);
  }

  public <__T> void Swap(dafny.TypeDescriptor<__T> _td___T, java.lang.Object a, java.math.BigInteger i, java.math.BigInteger j) {
    FisherYates.Implementation._Companion_Trait.Swap(_td___T, this, a, i, j);
  }
    
}
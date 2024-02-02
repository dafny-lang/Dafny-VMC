using System;
using System.Threading;
using System.Numerics;

namespace DafnyVMC {

  public class Random: DafnyVMCTrait.RandomTrait {
    static ThreadLocal<System.Random> RNG;
    
    public Random() {
      RNG = new ThreadLocal<System.Random>(createRandom);
    }

    public Random(System.Random rng) {
      RNG = new ThreadLocal<System.Random>(() => rng);
    }

    private static System.Random createRandom() {
      var rng = new System.Random();
      // Required for proper initialization
      rng.Next(2); 
      return rng;
    }

    public BigInteger UniformPowerOfTwoSample(BigInteger n) {
      if (n.Sign < 1) {
        throw new ArgumentException("n must be positive");
      }

      // Constructs a uniform random BigInteger in {0, ..., 2^k - 1)}, where k == n.GetBitLength() - 1.
      // E.g. for n = 8, we have k=3, since 2^{3} <= n < 2^{3+1}, and k == 3 == 4 - 1 = n.GetBitLength() - 1, as desired.
      // Next(m) returns a uniform random value in {0, ..., m - 1}.
      var m = (long) Math.Pow(2, n.GetBitLength() - 1); // converting double to long
      var o = RNG.Value.NextInt64(m);
      return new BigInteger(o);
    }
 
    public BigInteger UniformIntervalSample(BigInteger a, BigInteger b) {
      return Uniform.Interface._Companion_Trait.UniformIntervalSample(this, a, b);
    }

    public BigInteger UniformSample(BigInteger n) {
      return Uniform.Implementation._Companion_Trait.UniformSample(this, n);
    }

    public bool CoinSample() {
      return Coin.Implementation._Companion_Trait.CoinSample(this);
    }

    public bool BernoulliSample(Rationals._IRational p) {
      return Bernoulli.Implementation._Companion_Trait.BernoulliSample(this, p);
    }  

    public bool BernoulliExpNegSampleCaseLe1(Rationals._IRational gamma) {
      return BernoulliExpNeg.Implementation._Companion_Trait.BernoulliExpNegSampleCaseLe1(this, gamma);
    }

    public bool BernoulliExpNegSample(Rationals._IRational gamma) {
      return BernoulliExpNeg.Implementation._Companion_Trait.BernoulliExpNegSample(this, gamma);
    }

    public BigInteger DiscreteGaussianSample(Rationals._IRational sigma) {
      return DiscreteGaussian.Implementation._Companion_Trait.DiscreteGaussianSample(this, sigma);
    }

    public _System._ITuple2<bool, BigInteger> DiscreteLaplaceSampleLoop(Rationals._IRational scale) {
      return DiscreteLaplace.Implementation._Companion_Trait.DiscreteLaplaceSampleLoop(this, scale);
    }

    public BigInteger DisceteLaplaceSampleInnerLoop() {
      return DiscreteLaplace.Implementation._Companion_Trait.DisceteLaplaceSampleInnerLoop(this);
    }

    public BigInteger DiscreteLaplaceSample(Rationals._IRational scale) {
      return DiscreteLaplace.Implementation._Companion_Trait.DiscreteLaplaceSample(this, scale);
    }

    public void Shuffle<__T>(__T[] a) {
      FisherYates.Implementation._Companion_Trait.Shuffle(this, a);
    }
  }

}
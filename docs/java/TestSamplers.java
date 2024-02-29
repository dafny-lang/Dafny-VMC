import java.security.SecureRandom;
import java.math.BigInteger;
import java.util.Arrays;

import DafnyVMC.Random;

class TestSamplers {

    public static void main(String[] args) {

            /* STANDARD RNG */
            System.out.println("\nSTANDARD RNG TESTS\n");

            DafnyVMC.Random r = new DafnyVMC.Random();

            for (int i = 1; i < 10000; i++) {
                System.out.println("Testing Uniform");
                System.out.println(r.UniformSample(BigInteger.valueOf(i)));

                for (int j = 1; j <= i; i++) {
                    System.out.println("Testing Bernoulli");
                    System.out.println(r.BernoulliSample(i, j));
                    System.out.println(r.BernoulliSample(j, i));

                    System.out.println("Testing BernoulliExpNeg");
                    System.out.println(r.BernoulliExpNegSample(i, j));
                    System.out.println(r.BernoulliExpNegSample(j, i));

                    System.out.println("Testing DiscreteGaussian");
                    System.out.println(r.DiscreteGaussianSample(i, j));
                    System.out.println(r.DiscreteGaussianSample(j, i));
      
                    System.out.println("Testing DiscreteLaplace");
                    System.out.println(r.DiscreteLaplaceSample(i, j));
                    System.out.println(r.DiscreteLaplaceSample(j, i));
                }
            }

            /* CUSTOM RNG */
            System.out.println("\nCUSTOM RNG TESTS\n");

            SecureRandom rng = new SecureRandom();
            DafnyVMC.Random t = new DafnyVMC.Random(() -> rng);

            for (int i = 1; i < 10000; i++) {
                System.out.println("Testing Uniform");
                System.out.println(t.UniformSample(BigInteger.valueOf(i)));

                for (int j = 1; j <= i; i++) {
                    System.out.println("Testing Bernoulli");
                    System.out.println(t.BernoulliSample(i, j));
                    System.out.println(t.BernoulliSample(j, i));

                    System.out.println("Testing BernoulliExpNeg");
                    System.out.println(t.BernoulliExpNegSample(i, j));
                    System.out.println(t.BernoulliExpNegSample(j, i));

                    System.out.println("Testing DiscreteGaussian");
                    System.out.println(t.DiscreteGaussianSample(i, j));
                    System.out.println(t.DiscreteGaussianSample(j, i));
      
                    System.out.println("Testing DiscreteLaplace");
                    System.out.println(t.DiscreteLaplaceSample(i, j));
                    System.out.println(t.DiscreteLaplaceSample(j, i));
                }
            }


    }
}
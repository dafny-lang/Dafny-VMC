import java.security.SecureRandom;
import java.math.BigInteger;
import java.util.Arrays;

import DafnyVMC.Random;

class TestSamplers {

    public static void main(String[] args) {

            /* STANDARD RNG */
            System.out.println("\nSTANDARD RNG TESTS\n");

            DafnyVMC.Random r = new DafnyVMC.Random();

            for (int a = 1; a < 1000; a++) {
                BigInteger i = BigInteger.valueOf(a);

                System.out.println("Testing Uniform(" + a + ")");
                System.out.println(r.UniformSample(i));

                for (int b = 1; b <= a; b++) {
                    BigInteger j = BigInteger.valueOf(b);

                    System.out.println("Testing Bernoulli(" + a + "/" + b + ")");
                    System.out.println(r.BernoulliSample(i, j));
                    System.out.println("Testing Bernoulli(" + b + "/" + a + ")");
                    System.out.println(r.BernoulliSample(j, i));

                    System.out.println("Testing BernoulliExpNeg(" + a + "/" + b + ")");
                    System.out.println(r.BernoulliExpNegSample(i, j));
                    System.out.println("Testing BernoulliExpNeg(" + b + "/" + a + ")");
                    System.out.println(r.BernoulliExpNegSample(j, i));

                    System.out.println("Testing DiscreteGaussian(" + a + "/" + b + ")");
                    System.out.println(r.DiscreteGaussianSample(i, j));
                    System.out.println("Testing DiscreteGaussian(" + b + "/" + a + ")");
                    System.out.println(r.DiscreteGaussianSample(j, i));
      
                    System.out.println("Testing DiscreteLaPlace(" + a + "/" + b + ")");
                    System.out.println(r.DiscreteLaplaceSample(i, j));
                    System.out.println("Testing DiscreteLaPlace(" + b + "/" + a + ")");
                    System.out.println(r.DiscreteLaplaceSample(j, i));
                }
            }

            /* CUSTOM RNG */
            System.out.println("\nCUSTOM RNG TESTS\n");

            SecureRandom rng = new SecureRandom();
            DafnyVMC.Random t = new DafnyVMC.Random(() -> rng);

            for (int a = 1; a < 1000; a++) {
                BigInteger i = BigInteger.valueOf(a);
                System.out.println("Testing Uniform(" + a + ")");
                System.out.println(t.UniformSample(i));

                for (int b = 1; b <= a; b++) {
                    BigInteger j = BigInteger.valueOf(b);
                    System.out.println("Testing Bernoulli(" + a + "/" + b + ")");
                    System.out.println(t.BernoulliSample(i, j));
                    System.out.println("Testing Bernoulli(" + b + "/" + a + ")");
                    System.out.println(t.BernoulliSample(j, i));

                    System.out.println("Testing BernoulliExpNeg(" + a + "/" + b + ")");
                    System.out.println(t.BernoulliExpNegSample(i, j));
                    System.out.println("Testing BernoulliExpNeg(" + j + "/" + i + ")");
                    System.out.println(t.BernoulliExpNegSample(j, i));

                    System.out.println("Testing DiscreteGaussian(" + a + "/" + b + ")");
                    System.out.println(t.DiscreteGaussianSample(i, j));
                    System.out.println("Testing DiscreteGaussian(" + b + "/" + a + ")");
                    System.out.println(t.DiscreteGaussianSample(j, i));
      
                    System.out.println("Testing DiscreteLaPlace(" + a + "/" + b + ")");
                    System.out.println(t.DiscreteLaplaceSample(i, j));
                    System.out.println("Testing DiscreteLaPlace(" + b + "/" + a + ")");
                    System.out.println(t.DiscreteLaplaceSample(j, i));
                }
            }


    }
}
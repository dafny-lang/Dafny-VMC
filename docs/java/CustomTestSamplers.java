import java.security.SecureRandom;
import java.math.BigInteger;
import java.util.Arrays;

import DafnyVMC.Random;

class CustomTestSamplers {

    public static void main(String[] args) {

            /* STANDARD RNG */
            System.out.println("\n STANDARD RNG TESTS WITH CUSTOM UNIFORM\n");

            DafnyVMC.CustomRandom r = new DafnyVMC.CustomRandom();

            for (int a = 1; a < 1000; a++) {
                BigInteger i = BigInteger.valueOf(a);

                System.out.println("Testing Uniform(" + a + ")");
                System.out.println(r.UniformSample(i));

                for (int b = 1; b <= 1000; b++) {
                    BigInteger j = BigInteger.valueOf(b);

                    System.out.println("Testing Bernoulli(" + a + "/" + b + ")");
                    System.out.println(r.BernoulliSample(i, j));

                    System.out.println("Testing BernoulliExpNeg(" + a + "/" + b + ")");
                    System.out.println(r.BernoulliExpNegSample(i, j));

                    System.out.println("Testing DiscreteGaussian(" + a + "/" + b + ")");
                    System.out.println(r.DiscreteGaussianSample(i, j));
      
                    System.out.println("Testing DiscreteLaPlace(" + a + "/" + b + ")");
                    System.out.println(r.DiscreteLaplaceSample(i, j));
                }
            }

            // Edge cases

            BigInteger k = BigInteger.valueOf(1000000);
            BigInteger l = BigInteger.valueOf(1);

            System.out.println("Testing Bernoulli(1000000, 1)");
            System.out.println(r.BernoulliSample(k, l));
            System.out.println("Testing Bernoulli(1, 1000000)");
            System.out.println(r.BernoulliSample(l, k));

            System.out.println("Testing BernoulliExpNeg(1000000, 1)");
            System.out.println(r.BernoulliExpNegSample(k, l));
            System.out.println("Testing BernoulliExpNeg(1, 1000000)");
            System.out.println(r.BernoulliExpNegSample(l, k));

            System.out.println("Testing DiscreteGaussianSample(1000000, 1)");
            System.out.println(r.DiscreteGaussianSample(k, l));
            System.out.println("Testing DiscreteGaussianSample(1, 1000000)");
            System.out.println(r.DiscreteGaussianSample(l, k));

            System.out.println("Testing DiscreteLaplace(1000000, 1)");
            System.out.println(r.DiscreteLaplaceSample(k, l));
            System.out.println("Testing DiscreteLaplace(1, 1000000)");
            System.out.println(r.DiscreteLaplaceSample(l, k));

            /* CUSTOM RNG */
            System.out.println("\nCUSTOM RNG TESTS WITH CUSTOM UNIFORM\n");

            SecureRandom rng = new SecureRandom();
            DafnyVMC.CustomRandom t = new DafnyVMC.CustomRandom(() -> rng);

            for (int a = 1; a < 1000; a++) {
                BigInteger i = BigInteger.valueOf(a);
                System.out.println("Testing Uniform(" + a + ")");
                System.out.println(t.UniformSample(i));

                for (int b = 1; b <= 1000; b++) {
                    BigInteger j = BigInteger.valueOf(b);
                    System.out.println("Testing Bernoulli(" + a + "/" + b + ")");
                    System.out.println(t.BernoulliSample(i, j));

                    System.out.println("Testing BernoulliExpNeg(" + a + "/" + b + ")");
                    System.out.println(t.BernoulliExpNegSample(i, j));

                    System.out.println("Testing DiscreteGaussian(" + a + "/" + b + ")");
                    System.out.println(t.DiscreteGaussianSample(i, j));
      
                    System.out.println("Testing DiscreteLaPlace(" + a + "/" + b + ")");
                    System.out.println(t.DiscreteLaplaceSample(i, j));
                }
            }


            // Edge cases

            System.out.println("Testing Bernoulli(1000000, 1)");
            System.out.println(t.BernoulliSample(k, l));
            System.out.println("Testing Bernoulli(1, 1000000)");
            System.out.println(t.BernoulliSample(l, k));

            System.out.println("Testing BernoulliExpNeg(1000000, 1)");
            System.out.println(t.BernoulliExpNegSample(k, l));
            System.out.println("Testing BernoulliExpNeg(1, 1000000)");
            System.out.println(t.BernoulliExpNegSample(l, k));

            System.out.println("Testing DiscreteGaussianSample(1000000, 1)");
            System.out.println(t.DiscreteGaussianSample(k, l));
            System.out.println("Testing DiscreteGaussianSample(1, 1000000)");
            System.out.println(t.DiscreteGaussianSample(l, k));

            System.out.println("Testing DiscreteLaplace(1000000, 1)");
            System.out.println(t.DiscreteLaplaceSample(k, l));
            System.out.println("Testing DiscreteLaplace(1, 1000000)");
            System.out.println(t.DiscreteLaplaceSample(l, k));


    }
}
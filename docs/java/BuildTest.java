import java.security.SecureRandom;
import java.math.BigInteger;
import java.util.Arrays;

import DafnyVMC.Random;

class Check {
    public static void main(String[] args) {
        BigInteger[] arr1 = {BigInteger.valueOf(0), BigInteger.valueOf(1), BigInteger.valueOf(2)};
        int[] arr2 = {0, 1, 2};
        String[] arr3 = {"aa", "bb", "cc"};
        char[] arr4 = {'a', 'b', 'c'};
        boolean[] arr5 = {true, false, false, true};
        long[] arr6 = {111111L, 333333L, 999999L};
        short[] arr7 = {-3, 0, 3};
        BigInteger num = BigInteger.valueOf(1);
        BigInteger den = BigInteger.valueOf(1000);
        
        /* STANDARD RNG */
        System.out.println("\nSTANDARD RNG TESTS\n");
        
        DafnyVMC.Random r = new DafnyVMC.Random();

        System.out.println("Example of Uniform sampling");
        System.out.println(r.UniformSample(BigInteger.valueOf(4)));

        System.out.println("Example of Bernoulli sampling");
        System.out.println(r.BernoulliSample(num,den));

        System.out.println("Example of BernoulliExpNeg sampling");
        System.out.println(r.BernoulliExpNegSample(num,den));

        System.out.println("Example of DiscreteGaussian sampling");
        System.out.println(r.DiscreteGaussianSample(num,den));

        System.out.println("Example of DiscreteLaplace sampling");
        System.out.println(r.DiscreteLaplaceSample(num,den));

        System.out.println("Example of Fisher-Yates: BigInteger");
        r.Shuffle(arr1);
        System.out.println(Arrays.toString(arr1));
 
        System.out.println("Example of Fisher-Yates: int");
        r.Shuffle(arr2);
        System.out.println(Arrays.toString(arr2));

        System.out.println("Example of Fisher-Yates: String");
        r.Shuffle(arr3);
        System.out.println(Arrays.toString(arr3));

        System.out.println("Example of Fisher-Yates: char");
        r.Shuffle(arr4);
        System.out.println(Arrays.toString(arr4));

        System.out.println("Example of Fisher-Yates: boolean");
        r.Shuffle(arr5);
        System.out.println(Arrays.toString(arr5));

        System.out.println("Example of Fisher-Yates: long");
        r.Shuffle(arr6);
        System.out.println(Arrays.toString(arr6));

        System.out.println("Example of Fisher-Yates: short");
        r.Shuffle(arr7);
        System.out.println(Arrays.toString(arr7));

        /* CUSTOM RNG */
        System.out.println("\nCUSTOM RNG TESTS\n");

        SecureRandom rng = new SecureRandom();
        DafnyVMC.Random t = new DafnyVMC.Random(() -> rng);

        System.out.println("Example of Uniform sampling");
        System.out.println(t.UniformSample(BigInteger.valueOf(4)));

        System.out.println("Example of Bernoulli sampling");
        System.out.println(t.BernoulliSample(num,den));

        System.out.println("Example of BernoulliExpNeg sampling");
        System.out.println(r.BernoulliExpNegSample(num,den));

        System.out.println("Example of DiscreteGaussian sampling");
        System.out.println(t.DiscreteGaussianSample(num,den));

        System.out.println("Example of DiscreteLaplace sampling");
        System.out.println(t.DiscreteLaplaceSample(num,den));

        System.out.println("Example of Fisher-Yates: BigInteger");
        t.Shuffle(arr1);
        System.out.println(Arrays.toString(arr1));

        System.out.println("Example of Fisher-Yates: int");
        t.Shuffle(arr2);
        System.out.println(Arrays.toString(arr2));

        System.out.println("Example of Fisher-Yates: String");
        t.Shuffle(arr3);
        System.out.println(Arrays.toString(arr3));

        System.out.println("Example of Fisher-Yates: char");
        t.Shuffle(arr4);
        System.out.println(Arrays.toString(arr4));

        System.out.println("Example of Fisher-Yates: boolean");
        t.Shuffle(arr5);
        System.out.println(Arrays.toString(arr5));

        System.out.println("Example of Fisher-Yates: long");
        t.Shuffle(arr6);
        System.out.println(Arrays.toString(arr6));

        System.out.println("Example of Fisher-Yates: short");
        t.Shuffle(arr7);
        System.out.println(Arrays.toString(arr7));
    }
}
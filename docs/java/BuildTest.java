import java.security.SecureRandom;
import java.math.BigInteger;
import java.util.Arrays;

import DafnyVMC.Random;
import Uniform.Interface.TraitMinus;
import Uniform.Interface.Trait;

public class BuildTest {
    public static void main(String[] args) {
        BigInteger[] arr1 = {BigInteger.valueOf(0), BigInteger.valueOf(1), BigInteger.valueOf(2)};
        BigInteger[] arr1b = {BigInteger.valueOf(0), BigInteger.valueOf(1), BigInteger.valueOf(2)};
        int[] arr2 = {0, 1, 2};
        String[] arr3 = {"aa", "bb", "cc"};
        char[] arr4 = {'a', 'b', 'c'};
        boolean[] arr5 = {true, false, false, true};
        long[] arr6 = {111111L, 333333L, 999999L};
        short[] arr7 = {-3, 0, 3};
        BigInteger num = BigInteger.valueOf(3);
        BigInteger den = BigInteger.valueOf(5);

        DafnyVMC.Random r = new DafnyVMC.Random();
        Uniform.Interface.Trait t = new CustomUniformSample();
        Uniform.Interface.Trait t_faulty = new CustomUniformSampleFaulty();

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

        System.out.println("Example of custom Fisher-Yates: BigInteger");
        r.Shuffle(arr1, t);
        System.out.println(Arrays.toString(arr1));

        System.out.println("Example of faulty custom Fisher-Yates: BigInteger");
        r.Shuffle(arr1b, t_faulty);
        System.out.println(Arrays.toString(arr1b));
 
        System.out.println("Example of Fisher-Yates: int");
        r.Shuffle(arr2);
        System.out.println(Arrays.toString(arr2));

        System.out.println("Example of custom Fisher-Yates: int");
        r.Shuffle(arr2, t);
        System.out.println(Arrays.toString(arr2));

        System.out.println("Example of Fisher-Yates: String");
        r.Shuffle(arr3);
        System.out.println(Arrays.toString(arr3));

        System.out.println("Example of custom Fisher-Yates: String");
        r.Shuffle(arr3, t);
        System.out.println(Arrays.toString(arr3));

        System.out.println("Example of Fisher-Yates: char");
        r.Shuffle(arr4);
        System.out.println(Arrays.toString(arr4));

        System.out.println("Example of custom Fisher-Yates: char");
        r.Shuffle(arr4, t);
        System.out.println(Arrays.toString(arr4));

        System.out.println("Example of Fisher-Yates: boolean");
        r.Shuffle(arr5);
        System.out.println(Arrays.toString(arr5));

        System.out.println("Example of custom Fisher-Yates: boolean");
        r.Shuffle(arr5, t);
        System.out.println(Arrays.toString(arr5));

        System.out.println("Example of Fisher-Yates: long");
        r.Shuffle(arr6);
        System.out.println(Arrays.toString(arr6));

        System.out.println("Example of custom Fisher-Yates: long");
        r.Shuffle(arr6, t);
        System.out.println(Arrays.toString(arr6));

        System.out.println("Example of Fisher-Yates: short");
        r.Shuffle(arr7);
        System.out.println(Arrays.toString(arr7));

        System.out.println("Example of custom Fisher-Yates: short");
        r.Shuffle(arr7, t);
        System.out.println(Arrays.toString(arr7));
    }
}


import java.math.BigInteger;
import java.util.Arrays;

public class BuildTest {
    public static void main(String[] args) {
        BigInteger[] arr1 = {BigInteger.valueOf(0), BigInteger.valueOf(1), BigInteger.valueOf(2)};
        BigInteger[] arr1_custom = {BigInteger.valueOf(0), BigInteger.valueOf(1), BigInteger.valueOf(2)};
        BigInteger[] arr1_faulty = {BigInteger.valueOf(0), BigInteger.valueOf(1), BigInteger.valueOf(2)};
        int[] arr2 = {0, 1, 2};
        int[] arr2_custom = {0, 1, 2};
        int[] arr2_faulty = {0, 1, 2};
        String[] arr3 = {"aa", "bb", "cc"};
        String[] arr3_custom = {"aa", "bb", "cc"};
        String[] arr3_faulty = {"aa", "bb", "cc"};
        char[] arr4 = {'a', 'b', 'c'};
        char[] arr4_custom = {'a', 'b', 'c'};
        char[] arr4_faulty = {'a', 'b', 'c'};
        boolean[] arr5 = {true, false, false, true};
        boolean[] arr5_custom = {true, false, false, true};
        boolean[] arr5_faulty = {true, false, false, true};
        long[] arr6 = {111111L, 333333L, 999999L};
        long[] arr6_custom = {111111L, 333333L, 999999L};
        long[] arr6_faulty = {111111L, 333333L, 999999L};
        short[] arr7 = {-3, 0, 3};
        short[] arr7_custom = {-3, 0, 3};
        short[] arr7_faulty = {-3, 0, 3};
        BigInteger num = BigInteger.valueOf(3);
        BigInteger den = BigInteger.valueOf(5);

        DafnyVMC.Random r = new DafnyVMC.Random();
        CustomFisherYates r_custom = new CustomFisherYates();
        CustomFisherYatesFaulty r_faulty = new CustomFisherYatesFaulty();

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
        r_custom.Shuffle(arr1_custom);
        System.out.println(Arrays.toString(arr1_custom));

        System.out.println("Example of faulty custom Fisher-Yates: BigInteger");
        r_faulty.Shuffle(arr1_faulty);
        System.out.println(Arrays.toString(arr1_faulty));
 
        System.out.println("Example of Fisher-Yates: int");
        r.Shuffle(arr2);
        System.out.println(Arrays.toString(arr2));

        System.out.println("Example of custom Fisher-Yates: int");
        r_custom.Shuffle(arr2_custom);
        System.out.println(Arrays.toString(arr2_custom));

        System.out.println("Example of faulty custom Fisher-Yates: int");
        r_faulty.Shuffle(arr2_faulty);
        System.out.println(Arrays.toString(arr2_faulty));

        System.out.println("Example of Fisher-Yates: String");
        r.Shuffle(arr3);
        System.out.println(Arrays.toString(arr3));

        System.out.println("Example of custom Fisher-Yates: String");
        r_custom.Shuffle(arr3_custom);
        System.out.println(Arrays.toString(arr3_custom));

        System.out.println("Example of faulty custom Fisher-Yates: String");
        r_faulty.Shuffle(arr3_faulty);
        System.out.println(Arrays.toString(arr3_faulty));

        System.out.println("Example of Fisher-Yates: char");
        r.Shuffle(arr4);
        System.out.println(Arrays.toString(arr4));

        System.out.println("Example of custom Fisher-Yates: char");
        r_custom.Shuffle(arr4_custom);
        System.out.println(Arrays.toString(arr4_custom));

        System.out.println("Example of faulty custom Fisher-Yates: char");
        r_faulty.Shuffle(arr4_faulty);
        System.out.println(Arrays.toString(arr4_faulty));

        System.out.println("Example of Fisher-Yates: boolean");
        r.Shuffle(arr5);
        System.out.println(Arrays.toString(arr5));

        System.out.println("Example of custom Fisher-Yates: boolean");
        r_custom.Shuffle(arr5_custom);
        System.out.println(Arrays.toString(arr5_custom));

        System.out.println("Example of faulty custom Fisher-Yates: boolean");
        r_faulty.Shuffle(arr5_faulty);
        System.out.println(Arrays.toString(arr5_faulty));

        System.out.println("Example of Fisher-Yates: long");
        r.Shuffle(arr6);
        System.out.println(Arrays.toString(arr6));

        System.out.println("Example of custom Fisher-Yates: long");
        r_custom.Shuffle(arr6_custom);
        System.out.println(Arrays.toString(arr6_custom));

        System.out.println("Example of faulty custom Fisher-Yates: long");
        r_faulty.Shuffle(arr6_faulty);
        System.out.println(Arrays.toString(arr6_faulty));

        System.out.println("Example of Fisher-Yates: short");
        r.Shuffle(arr7);
        System.out.println(Arrays.toString(arr7));

        System.out.println("Example of custom Fisher-Yates: short");
        r_custom.Shuffle(arr7_custom);
        System.out.println(Arrays.toString(arr7_custom));

        System.out.println("Example of faulty custom Fisher-Yates: short");
        r_faulty.Shuffle(arr7_faulty);
        System.out.println(Arrays.toString(arr7_faulty));
    }
}


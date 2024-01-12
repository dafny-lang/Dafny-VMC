import DafnyVMC.Random;
import DafnyVMC.RandomCoin;

import java.math.BigInteger;
import java.util.Arrays;

class Check {
    public static void main(String[] args) {
        BigInteger[] arr1 = {BigInteger.valueOf(0), BigInteger.valueOf(1), BigInteger.valueOf(2)};
        int[] arr2 = {0, 1, 2};
        String[] arr3 = {"aa", "bb", "cc"};
        char[] arr4 = {'a', 'b', 'c'};
        boolean[] arr5 = {true, false, false, true};
        long[] arr6 = {111111L, 333333L, 999999L};
        short[] arr7 = {-3, 0, 3};
        
        // Tests with UniformPowerOfTwo as primitive
        DafnyVMC.Random r = new DafnyVMC.Random();

        System.out.println("Example of Uniform sampling");
        System.out.println(r.UniformSample(BigInteger.valueOf(4)));

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

        // Tests with Coin as primitive
        DafnyVMC.RandomCoin s = new DafnyVMC.RandomCoin();

        System.out.println("Example of Uniform sampling");
        System.out.println(s.UniformSample(BigInteger.valueOf(4)));

        System.out.println("Example of Fisher-Yates: BigInteger");
        s.Shuffle(arr1);
        System.out.println(Arrays.toString(arr1));

        System.out.println("Example of Fisher-Yates: int");
        s.Shuffle(arr2);
        System.out.println(Arrays.toString(arr2));

        System.out.println("Example of Fisher-Yates: String");
        s.Shuffle(arr3);
        System.out.println(Arrays.toString(arr3));

        System.out.println("Example of Fisher-Yates: char");
        s.Shuffle(arr4);
        System.out.println(Arrays.toString(arr4));

        System.out.println("Example of Fisher-Yates: boolean");
        s.Shuffle(arr5);
        System.out.println(Arrays.toString(arr5));

        System.out.println("Example of Fisher-Yates: long");
        s.Shuffle(arr6);
        System.out.println(Arrays.toString(arr6));

        System.out.println("Example of Fisher-Yates: short");
        s.Shuffle(arr7);
        System.out.println(Arrays.toString(arr7));

    }
}
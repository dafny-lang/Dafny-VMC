import java.security.SecureRandom;
import java.math.BigInteger;
import java.util.Arrays;

import DafnyVMC.Random;

class TestShuffling32 {
    public static void main(String[] args) {
        BigInteger[] arr1 = {BigInteger.valueOf(0), BigInteger.valueOf(1), BigInteger.valueOf(2)};
        int[] arr2 = {0, 1, 2};
        String[] arr3 = {"aa", "bb", "cc"};
        char[] arr4 = {'a', 'b', 'c'};
        boolean[] arr5 = {true, false, false, true};
        long[] arr6 = {111111L, 333333L, 999999L};
        short[] arr7 = {-3, 0, 3};
        

        /* STANDARD RNG */
        System.out.println("\nSTANDARD RNG TESTS WITH CUSTOM UNIFORM\n");

        DafnyVMC.Random r = new DafnyVMC.Random();

        System.out.println("Example of Fisher-Yates: BigInteger");
        r.Shuffle32(arr1);
        System.out.println(Arrays.toString(arr1));
 
        System.out.println("Example of Fisher-Yates: int");
        r.Shuffle32(arr2);
        System.out.println(Arrays.toString(arr2));

        System.out.println("Example of Fisher-Yates: String");
        r.Shuffle32(arr3);
        System.out.println(Arrays.toString(arr3));

        System.out.println("Example of Fisher-Yates: char");
        r.Shuffle32(arr4);
        System.out.println(Arrays.toString(arr4));

        System.out.println("Example of Fisher-Yates: boolean");
        r.Shuffle32(arr5);
        System.out.println(Arrays.toString(arr5));

        System.out.println("Example of Fisher-Yates: long");
        r.Shuffle32(arr6);
        System.out.println(Arrays.toString(arr6));

        System.out.println("Example of Fisher-Yates: short");
        r.Shuffle32(arr7);
        System.out.println(Arrays.toString(arr7));

        /* CUSTOM RNG */
        System.out.println("\nCUSTOM RNG TESTS WITH CUSTOM UNIFORM\n");

        SecureRandom rng = new SecureRandom();
        DafnyVMC.Random t = new DafnyVMC.Random(() -> rng);

        System.out.println("Example of Fisher-Yates: BigInteger");
        t.Shuffle32(arr1);
        System.out.println(Arrays.toString(arr1));

        System.out.println("Example of Fisher-Yates: int");
        t.Shuffle32(arr2);
        System.out.println(Arrays.toString(arr2));

        System.out.println("Example of Fisher-Yates: String");
        t.Shuffle32(arr3);
        System.out.println(Arrays.toString(arr3));

        System.out.println("Example of Fisher-Yates: char");
        t.Shuffle32(arr4);
        System.out.println(Arrays.toString(arr4));

        System.out.println("Example of Fisher-Yates: boolean");
        t.Shuffle32(arr5);
        System.out.println(Arrays.toString(arr5));

        System.out.println("Example of Fisher-Yates: long");
        t.Shuffle32(arr6);
        System.out.println(Arrays.toString(arr6));

        System.out.println("Example of Fisher-Yates: short");
        t.Shuffle32(arr7);
        System.out.println(Arrays.toString(arr7));
    }
}
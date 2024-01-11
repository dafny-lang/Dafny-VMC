import DafnyVMC.*;
import dafny.TypeDescriptor;
import java.math.BigInteger;
import java.util.Arrays;
import FisherYatesTest.DRandomExternUniformPowerOfTwoPlus;

class Check {
    public static void main(String[] args) {
        DRandomExternUniformPowerOfTwoPlus d = new DRandomExternUniformPowerOfTwoPlus();

        System.out.println("Example of Uniform sampling");
        System.out.println(d.UniformSample(BigInteger.valueOf(4)));

        System.out.println("Example of Fisher-Yates: BigInteger");
        BigInteger[] arr1 = {BigInteger.valueOf(0), BigInteger.valueOf(1), BigInteger.valueOf(2)};

        d.Shuffle(TypeDescriptor.BIG_INTEGER, arr1);
        System.out.println(Arrays.toString(arr1));

        d.ShuffleBigInteger(arr1);
        System.out.println(Arrays.toString(arr1));

        d.DShuffle(arr1);
        System.out.println(Arrays.toString(arr1));

        System.out.println("Example of Fisher-Yates: int");
        int[] arr2 = {0, 1, 2};
        d.Shuffle(TypeDescriptor.INT, arr2);
        System.out.println(Arrays.toString(arr2));

        System.out.println("Example of Fisher-Yates: String");
        String[] arr3 = {"aa", "bb", "cc"};

        d.Shuffle(TypeDescriptor.CHAR_ARRAY, arr3);
        System.out.println(Arrays.toString(arr3));

        d.DShuffle(arr3);
        System.out.println(Arrays.toString(arr3));

        System.out.println("Example of Fisher-Yates: char");
        char[] arr4 = {'a', 'b', 'c'};

        d.Shuffle(TypeDescriptor.CHAR, arr4);
        System.out.println(Arrays.toString(arr4));

        System.out.println("Example of Fisher-Yates: boolean");
        boolean[] arr5 = {true, false, false, true};

        d.Shuffle(TypeDescriptor.BOOLEAN, arr5);
        System.out.println(Arrays.toString(arr5));

        d.ShuffleBool(arr5);
        System.out.println(Arrays.toString(arr5));

        System.out.println("Example of Fisher-Yates: long");
        long[] arr6 = {111111L, 333333L, 999999L};

        d.Shuffle(TypeDescriptor.LONG, arr6);
        System.out.println(Arrays.toString(arr6));

        System.out.println("Example of Fisher-Yates: short");
        short[] arr7 = {-3, 0, 3};
        d.Shuffle(TypeDescriptor.SHORT, arr7);
        System.out.println(Arrays.toString(arr7));

    }
}
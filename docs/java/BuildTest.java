import DafnyVMC.*;
import java.math.BigInteger;

class Check {
    public static void main(String[] args) {
        DRandomExternUniformPowerOfTwo d = new DRandomExternUniformPowerOfTwo();
        System.out.println(d.UniformSample(BigInteger.valueOf(4))); 
    }
}
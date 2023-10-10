import DafnyVMC.*;
import java.math.BigInteger;

class Check {
    public static void main(String[] args) {
        DRandomExternUniform d = new DRandomExternUniform();
        System.out.println(d.UniformSample(BigInteger.valueOf(4))); 
    }
}
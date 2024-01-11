package FisherYatesTest;

import DafnyVMC.DRandomExternUniformPowerOfTwo;
import dafny.TypeDescriptor;
import java.math.BigInteger;


public class DRandomExternUniformPowerOfTwoPlus extends DRandomExternUniformPowerOfTwo {
  public void DShuffle(BigInteger[] arr) {
    this.Shuffle(TypeDescriptor.BIG_INTEGER, arr);
  }

  public void DShuffle(String[] arr) {
    this.Shuffle(TypeDescriptor.CHAR_ARRAY, arr);
  }
}
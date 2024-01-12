package DafnyVMC;

import dafny.TypeDescriptor;
import java.math.BigInteger;

public class Random extends DafnyVMCMinus.Random {
  public void Shuffle(BigInteger[] arr) {
    this.Shuffle(TypeDescriptor.BIG_INTEGER, arr);
  }

  public void Shuffle(int[] arr) {
    this.Shuffle(TypeDescriptor.INT, arr);
  }

  public void Shuffle(String[] arr) {
    this.Shuffle(TypeDescriptor.CHAR_ARRAY, arr);
  }

  public void Shuffle(char[] arr) {
    this.Shuffle(TypeDescriptor.CHAR, arr);
  }

  public void Shuffle(boolean[] arr) {
    this.Shuffle(TypeDescriptor.BOOLEAN, arr);
  }

  public void Shuffle(long[] arr) {
    this.Shuffle(TypeDescriptor.LONG, arr);
  }

  public void Shuffle(short[] arr) {
    this.Shuffle(TypeDescriptor.SHORT, arr);
  }
}
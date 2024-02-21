/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module BernoulliExpNeg.Implementation {
  import Interface
  import opened Pos

  trait {:termination false} Trait extends Interface.Trait {

    method BernoulliExpNegSampleUnitLoop (num: nat, den: pos, state: (bool,pos))
      returns (o: (bool,pos))
      requires num <= den
      modifies this
      decreases *
    {
      var A := BernoulliSample(num, state.1 * den);
      o := (A,state.1 + 1);
    }

    method BernoulliExpNegSampleUnitAux (num: nat, den: pos)
      returns (o: nat)
      requires num <= den
      modifies this
      decreases *
    {
      var state := (true,1);
      while state.0
        decreases *
      {
        state := BernoulliExpNegSampleUnitLoop(num, den, state);
      }
      var r := state;
      o := r.1;
    }

    method BernoulliExpNegSampleUnit (num: nat, den: pos)
      returns (o: bool)
      requires num <= den
      modifies this
      decreases *
    {
      var K := BernoulliExpNegSampleUnitAux(num, den);
      if K % 2 == 0 {
        o := true;
      } else {
        o := false;
      }
    }

    method BernoulliExpNegSampleGenLoop (iter: nat)
      returns (o: bool)
      modifies this
      decreases *
    {
      if iter == 0 {
        o := true;
      } else {
        var B := BernoulliExpNegSampleUnit(1, 1);
        var R := BernoulliExpNegSampleGenLoop(iter - 1);
        o := B == true && R == true;
      }
    }

    method BernoulliExpNegSample (num: nat, den: pos)
      returns (o: bool)
      modifies this
      decreases *
    {
      if num <= den {
        var X := BernoulliExpNegSampleUnit(num, den);
        o := X;
      } else {
        var gamf := num / den;
        var B := BernoulliExpNegSampleGenLoop(gamf);
        if B == true {
          var num := num - gamf * den;
          var X := BernoulliExpNegSampleUnit(num, den);
          o := X;
        } else {
          o := false;
        }
      }
    }

  }

}
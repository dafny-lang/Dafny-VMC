/*******************************************************************************
*  Copyright by the contributors to the Dafny Project
*  SPDX-License-Identifier: MIT
*******************************************************************************/

// RUN: %verify "%s"

include "../Library/DRandom.dfy"

module RandomExamples {
  import opened DafnyLibraries

  method Main() 
    decreases *
  {
    var r := new DRandom();

    for i := 0 to 20 {
      var b := r.Coin();
      print b, "\n";
    }

    print "\n";

    for i := 0 to 20 {
      var u := r.Uniform(10);
      print u, "\n";
    }

    print "\n";

    for i := 0 to 20 {
      var u := r.UniformInterval(3, 6);
      print u, "\n";
    }

    print "\n";

    for i := 0 to 20 {
      var u := r.Geometric();
      print u, "\n";
    }

    print "\n";

    for i := 0 to 20 {
      var u := r.Bernoulli(0.2);
      print u, "\n";
    }
  }
}
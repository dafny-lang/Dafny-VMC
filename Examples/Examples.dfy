/*******************************************************************************
*  Copyright by the contributors to the Dafny Project
*  SPDX-License-Identifier: MIT
*******************************************************************************/

// RUN: %verify "%s"

include "./Library/Random.dfy"

module RandomExamples {
  import opened DafnyLibraries

  method Main() {
    var r := new Random();

    for i := 0 to 9 {
      var b := r.Coin();
      print b, "\n";
    }

    print "\n";

    for i := 0 to 9 {
      var u := r.Uniform(9);
      print u, "\n";
    }

    print "\n";

    for i := 0 to 9 {
      var u := r.UniformInterval(3, 6);
      print u, "\n";
    }
  }
}
#!/bin/bash

if [ -z ${DAFNY+x} ]
then
  echo "Set the DAFNY variable"
  exit 1  
fi

echo Verification of the proofs
for file in `find ./src -type f -name '*.dfy'`
do
    echo Verifying $file
    #$DAFNY verify $file
done

echo Running C\# tests
$DAFNY test --target:cs src/DRandomCoin.cs src/DRandomUniform.cs tests/TestsFoundational.dfy
$DAFNY test --target:cs src/DRandomCoin.cs src/DRandomUniform.cs tests/TestsExternUniform.dfy

echo Running C\# documentation
$DAFNY run docs/ExamplesFoundational.dfy --target:cs --input src/DRandomCoin.cs --input src/DRandomUniform.cs
$DAFNY run docs/ExamplesExternUniform.dfy --target:cs --input src/DRandomCoin.cs --input src/DRandomUniform.cs

echo Running Java tests
$DAFNY test --target:java src/DRandomCoin.java src/DRandomUniform.java tests/TestsFoundational.dfy
$DAFNY test --target:java src/DRandomCoin.java src/DRandomUniform.java tests/TestsExternUniform.dfy

echo Running Java documentation
$DAFNY run docs/ExamplesFoundational.dfy --target:java --input src/DRandomCoin.java --input src/DRandomUniform.java
$DAFNY run docs/ExamplesExternUniform.dfy --target:java --input src/DRandomCoin.java --input src/DRandomUniform.java
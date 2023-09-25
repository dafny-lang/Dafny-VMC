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
    $DAFNY verify $file
done

echo Running tests
$DAFNY test --target:java src/DRandom.java tests/Tests.dfy
$DAFNY test --target:cs src/DRandom.cs tests/Tests.dfy

echo Running documentation
$DAFNY run docs/Examples.dfy --target:java --input src/DRandom.java
$DAFNY run docs/Examples.dfy --target:cs --input src/DRandom.cs

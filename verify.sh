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
$DAFNY test --target:cs src/DRandom.cs tests/TestsFoundational.dfy
$DAFNY test --target:cs src/DRandom.cs tests/TestsExternUniform.dfy

echo Running documentation
$DAFNY run docs/ExamplesFoundational.dfy --target:cs --input src/DRandom.cs
$DAFNY run docs/ExamplesExternUniform.dfy --target:cs --input src/DRandom.cs

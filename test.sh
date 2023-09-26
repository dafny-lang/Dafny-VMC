#!/bin/bash

set -e

if [ -z ${DAFNY+x} ]
then
  echo "Set the DAFNY variable"
  exit 1
fi

echo Running tests...
echo "Running tests/TestsFoundational.dfy:"
time $DAFNY test --target:cs src/DRandom.cs tests/TestsFoundational.dfy
echo "Running tests/TestsExternUniform.dfy:"
time $DAFNY test --target:cs src/DRandom.cs tests/TestsExternUniform.dfy

echo Running documentation...
echo "Running docs/ExamplesFoundational.dfy"
$DAFNY run docs/ExamplesFoundational.dfy --target:cs --input src/DRandom.cs
echo "docs/ExamplesExternUniform.dfy"
$DAFNY run docs/ExamplesExternUniform.dfy --target:cs --input src/DRandom.cs

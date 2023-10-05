#!/bin/bash

set -e

if [ -z ${DAFNY+x} ]
then
  echo "Set the DAFNY variable"
  exit 1
fi

echo Verifying the proofs...
time $DAFNY verify dfyconfig.toml
time $DAFNY verify docs/dafny/ExamplesExternUniform.dfy
time $DAFNY verify docs/dafny/ExamplesFoundational.dfy
time $DAFNY verify tests/Tests.dfy
time $DAFNY verify tests/TestsExternUniform.dfy
time $DAFNY verify tests/TestsFoundational.dfy
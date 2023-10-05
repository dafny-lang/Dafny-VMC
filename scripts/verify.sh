#!/bin/bash

set -e

if [ -z ${DAFNY+x} ]
then
  echo "Set the DAFNY variable"
  exit 1
fi

echo Verifying the proofs...
time $DAFNY verify dfyconfig.toml docs/dafny/ExamplesExternUniform.dfy docs/dafny/ExamplesFoundational.dfy tests/Tests.dfy tests/TestsExternUniform.dfy tests/TestsFoundational.dfy
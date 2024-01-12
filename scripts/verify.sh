#!/bin/bash

set -e

if [ -z ${DAFNY+x} ]
then
  echo "Set the DAFNY variable"
  exit 1
fi

echo Verifying the proofs...
time $DAFNY verify dfyconfig.toml docs/dafny/ExamplesRandom.dfy docs/dafny/ExamplesRandomCoin.dfy tests/Tests.dfy tests/TestsRandom.dfy tests/TestsRandomCoin.dfy --resource-limit 20000 # 20M resource usage

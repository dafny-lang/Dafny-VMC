#!/bin/bash

set -e

if [ -z ${DAFNY+x} ]
then
  echo "Set the DAFNY variable"
  exit 1
fi

echo Verifying the proofs...
for file in `find ./src -type f -name '*.dfy'`
do
    echo Verifying $file...
    time $DAFNY verify $file
done

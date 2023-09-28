#!/bin/bash

set -e

if [ -z ${DAFNY+x} ]
then
  echo "Set the DAFNY variable"
  exit 1
fi

echo '\n' > audit.log

for file in `find ./src -type f -name '*.dfy'`
do
  echo Auditing $file >> audit.log
  $DAFNY audit $file | grep -v '{:termination false}\|{:extern}\|decreases *\|Dafny auditor completed\|Dafny program verifier' | sed 's/.*Warning://' | sed 's/Possible.*//' >> audit.log
done
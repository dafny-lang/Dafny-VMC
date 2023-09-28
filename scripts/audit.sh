#!/bin/bash

set -e

if [ -z ${DAFNY+x} ]
then
  echo "Set the DAFNY variable"
  exit 1
fi

for file in `find ./src -type f -name '*.dfy'`
do
  echo Auditing $file 
  #cat $file | grep "axiom"
  #cat $file | grep "assume"
  $DAFNY audit $file | grep -v '{:termination false}\|{:extern}\|decreases *\|Dafny auditor completed\|Dafny program verifier' | sed 's/.*Warning://' | sed 's/Possible.*//'
done 
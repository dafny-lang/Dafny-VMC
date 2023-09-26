#!/bin/bash

set -e

if [ -z ${DAFNY+x} ]
then
  echo "Set the DAFNY variable"
  exit 1
fi

if [ -z ${LANG+x} ]
then
  echo "Set the LANG variable"
  exit 1
fi

$DAFNY build --target:$LANG interop/$LANG/DRandomCoin.$LANG interop/$LANG/DRandomUniform.$LANG src/Dafny-VMC.dfy -o build/$LANG/Dafny-VMC

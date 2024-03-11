#!/bin/bash

set -e

if [ -z ${DAFNY+x} ]
then
  echo "Set the DAFNY variable"
  exit 1
fi

if [ -z ${DAFNYSOURCE+x} ]
then
  echo "Set the DAFNYSOURCE variable"
  exit 1
fi

echo Generating Dafny documentation...
$DAFNY doc dfyconfig.toml --output docs/dafny/dafny-doc/

echo Generating Java documentation...
dafny translate java src/interop/java/Full/CustomRandom.java src/interop/java/Full/Random.java dfyconfig.toml -o src/DafnyVMC --no-verify --include-runtime
mkdir src/DafnyVMC-java/DafnyVMC
cp src/interop/java/Full/CustomRandom.java src/DafnyVMC-java/DafnyVMC
cp src/interop/java/Full/Random.java src/DafnyVMC-java/DafnyVMC
find src/DafnyVMC-java/ -type f -name "*.java" | xargs javadoc -d docs/java/java-doc/

echo Generating Python documentation...
export TARGET_LANG=py
bash scripts/build.sh
PYTHONPATH=.:build/py/DafnyVMC-py pydoc3 -w build/py/DafnyVMC-py/DafnyVMC.py
mv *.html docs/py/py-doc
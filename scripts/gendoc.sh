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
$DAFNY doc src/Dafny-VMC.dfy --output docs/dafny/dafny-doc/

echo Generating Java documentation...
$DAFNY translate java src/Dafny-VMC.dfy 
cp $DAFNYSOURCE/Source/DafnyRuntime/DafnyRuntimeJava/src/main/java/dafny/*.java src/Dafny-VMC-java/dafny/
javadoc -d docs/java/java-doc/ -sourcepath src/Dafny-VMC-java -package DafnyVMC
#!/bin/bash

VERSION=https://github.com/dafny-lang/dafny/archive/refs/tags/v4.3.0.zip

wget $VERSION
unzip `basename $VERSION` 

mv dafny-4.3.0 dafny
cd dafny
make exe
cd ..
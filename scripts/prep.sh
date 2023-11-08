#!/bin/bash

VERSION=https://github.com/dafny-lang/dafny/releases/download/v4.3.0/dafny-4.3.0-x64-ubuntu-20.04.zip

wget $VERSION
unzip `basename $VERSION` 

cd dafny
dotnet add package System.Security.Cryptography.Algorithms --version 4.3.1
cd ..
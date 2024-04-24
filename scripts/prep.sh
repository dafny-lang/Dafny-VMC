#!/bin/bash

VERSION=https://github.com/dafny-lang/dafny/releases/download/v4.4.0/dafny-4.4.0-x64-ubuntu-20.04.zip

wget $VERSION
unzip `basename $VERSION` 

curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf -y | sh

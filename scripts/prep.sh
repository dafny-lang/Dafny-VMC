#!/bin/bash

VERSION=https://github.com/dafny-lang/dafny/releases/download/v4.2.0/dafny-4.2.0-x64-ubuntu-20.04.zip

wget $VERSION
unzip `basename $VERSION` 
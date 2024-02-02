#!/bin/bash

rm -f build/cs/DafnyVMC.cs
cp docs/cs/BuildTest.cs build/cs/
dotnet run --project build/cs/cs.csproj
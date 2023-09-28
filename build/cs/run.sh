#!/bin/bash

rm -f build/cs/Dafny-VMC.cs
cp docs/csharp/BuildTest.cs build/cs/
dotnet run --project build/cs/cs.csproj
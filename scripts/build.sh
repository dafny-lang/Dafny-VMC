
DAFNY=dafny
LANG=java

$DAFNY build --target:$LANG interop/$LANG/DRandomCoin.$LANG interop/$LANG/DRandomUniform.$LANG src/Dafny-VMC.dfy -o build/$LANG/Dafny-VMC.jar
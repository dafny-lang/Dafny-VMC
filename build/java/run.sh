#1/bin/bash
javac -classpath "build/java/DafnyVMC.jar:docs/java/" docs/java/CustomUniformSample.java docs/java/CustomUniformSampleFaulty.java
java -classpath "build/java/DafnyVMC.jar:docs/java/" docs/java/BuildTest.java 

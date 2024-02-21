#1/bin/bash
javac -classpath "build/java/DafnyVMC.jar:docs/java/" docs/java/CustomFisherYates.java docs/java/CustomFisherYatesFaulty.java
java -classpath "build/java/DafnyVMC.jar:docs/java/" docs/java/BuildTest.java 

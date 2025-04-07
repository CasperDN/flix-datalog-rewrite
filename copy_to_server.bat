@echo off
set "jar=flix-datalog-rewrite.jar"
echo Building jar...
java -jar flix.jar build --entrypoint mainBTreeExperiment
java -jar flix.jar build-jar --entrypoint mainBTreeExperiment

echo Sending to server...
scp artifact/%jar% flixserver:
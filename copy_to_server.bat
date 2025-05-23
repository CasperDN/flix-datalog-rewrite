@echo off
set "jar=flix-datalog-rewrite.jar"
echo Building jar...
java -jar flix.jar build --entrypoint benchmark
java -jar flix.jar build-jar --entrypoint benchmark

echo Sending to server...
scp artifact/%jar% flixserver:

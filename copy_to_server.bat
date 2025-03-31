@echo off
set "jar=flix-datalog-rewrite.jar"
echo Building jar...
java -jar flix.jar build --entrypoint mainBinarySearch
java -jar flix.jar build-jar --entrypoint mainBinarySearch

echo Sending to server...
scp artifact/%jar% flixserver:
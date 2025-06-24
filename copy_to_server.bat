@echo off
set "jar=flix-datalog-rewrite.jar"
echo Building jar...
java -jar flix.jar build --entrypoint main444
java -jar flix.jar build-jar --entrypoint main444

echo Sending to server...
scp artifact/%jar% flixserver:

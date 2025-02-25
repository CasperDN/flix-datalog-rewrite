@echo off
setlocal EnableDelayedExpansion
set lf= data/
for /F "delims=" %%i in ('cmd /r dir data /b') do if ("!files!"=="") (set files=%%i) else (set files=!files!%lf%%%i)

set "files=dep\seaborn-data\titanic.csv %files%"
set "jar=flix-datalog-rewrite.jar"
echo Building jar...
java -jar flix.jar build --entrypoint benchmark
java -jar flix.jar build-jar --entrypoint benchmark

echo Sending to server...
scp artifact/%jar% %files% flixserver:
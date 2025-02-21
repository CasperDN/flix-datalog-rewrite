@echo off
set "files=dep\seaborn-data\titanic.csv src\Test\edge.csv"
set "jar=flix-datalog-rewrite.jar"
set "program=Path"

java -jar flix.jar build --entrypoint benchmark
java -jar flix.jar build-jar --entrypoint benchmark

scp artifact/%jar% %files% flixserver:
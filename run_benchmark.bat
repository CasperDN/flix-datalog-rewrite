@echo off
set "jar=flix-datalog-rewrite.jar"
echo Running benchmark...
ssh flixserver "java -jar %jar% > output.txt"
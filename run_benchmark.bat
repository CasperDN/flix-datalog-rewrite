@echo off
set "jar=flix-datalog-rewrite.jar"
set "program=Road"
echo Running benchmark...
ssh flixserver "java -jar %jar% %program% > output.txt"
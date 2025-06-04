@echo off
set "jar=flix-datalog-rewrite.jar"
set "program=All"
echo Running benchmark...
ssh flixserver "java -jar %jar% %program% > output.txt"
@echo off
set "jar=flix-datalog-rewrite.jar"
set "program=Path"
echo Running benchmark...
ssh flixserver "java -jar %jar% %program%"
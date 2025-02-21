@echo off
set "jar=flix-datalog-rewrite.jar"
set "program=Path"
ssh flixserver "java -jar %jar% %program%"
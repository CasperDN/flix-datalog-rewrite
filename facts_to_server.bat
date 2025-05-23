@echo off
set "facts_folder=facts"
echo Sending facts to server...
scp -r %facts_folder% flixserver
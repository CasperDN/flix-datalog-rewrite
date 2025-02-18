set "f=flix-datalog-rewrite"
set "out=%f%.zip"
set "program=Path"
ssh flixserver "tar --recursive-unlink -xvf %out% ; cd %f% || exit ; ./run_server.sh %program%" > file.txt
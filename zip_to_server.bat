set "f=flix-datalog-rewrite"
set "out=%f%.zip"
cd ..
tar -a -c --exclude="%f%/.git" %f% > %out%
scp %out% caspe@37.27.96.169:
if exist %out% del %out% 

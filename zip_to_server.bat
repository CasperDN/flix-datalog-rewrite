cd ..
tar -a -c --exclude="flix-datalog-rewrite/.git" flix-datalog-rewrite > out.zip
scp out.zip caspe@37.27.96.169:
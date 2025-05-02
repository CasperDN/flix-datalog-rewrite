set "road=roadNet-CA.txt"
curl https://snap.stanford.edu/data/roadNet-CA.txt.gz
7z e road.gz
del road
move road data


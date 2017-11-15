#!/bin/bash

rm -f example2.tar
rm -f out.txt
wget http://bagpipe.uwplse.org/bagpipe/assets/example2.tar
cat example2.tar | bagpipe verify no-martian disable-martian-checks kans atla > out.txt

success=0
if [ `grep "policy does not hold" out.txt | wc -l` -ne 0 ]; then
    success=1
fi

rm -f example2.tar
rm -f out.txt
exit $success

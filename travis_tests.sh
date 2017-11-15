#!/bin/bash

rm -f example2.tar
rm -f out.txt
wget http://bagpipe.uwplse.org/bagpipe/assets/example2.tar
cat example2.tar | bagpipe verify no-martian disable-martian-checks kans atla > out.txt 2> /dev/null

exit_code=1
if [ `grep "policy does not hold" out.txt | wc -l` -ne 0 ]; then
    exit_code=0
fi

rm -f example2.tar
rm -f out.txt
exit $exit_code

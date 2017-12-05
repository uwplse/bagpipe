#!/bin/bash

rm -f example2.tar
rm -f out.txt
rm -f error.txt

wget http://bagpipe.uwplse.org/bagpipe/assets/example2.tar
cat example2.tar | bagpipe verify no-martian disable-martian-checks kans atla > out.txt 2> error.txt

exit_code=1
if [ `grep "policy does not hold" out.txt | wc -l` -ne 0 ]; then
    cat error.txt
    exit_code=0
fi

rm -f example2.tar
rm -f out.txt
rm -f error.txt
exit $exit_code

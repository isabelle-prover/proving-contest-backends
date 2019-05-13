#!/bin/bash

mkdir /tmp/HOL4-grader

cd /tmp/HOL4-grader
cp /var/lib/HOL4-grader/checkScript.sml .
cp /var/lib/HOL4-grader/definitionsScript.sml .
cp /var/lib/HOL4-grader/templateScript.sml .

res=`~/repos/git/HOL/bin/Holmake`

if grep -qv FAILED <<< $res ; then
 echo "Success"
 echo $res
 exitcode=4
else
 echo "Failed to build proof scripts..."
 echo $res
 exitcode=5
fi


# tidy up
rm -rf /tmp/HOL4-grader

exit $exitcode

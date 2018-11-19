#!/bin/bash

cd /var/lib/HOL4-grader

res=`~/repos/git/HOL/bin/Holmake`

if grep -qv FAILED <<< $res ; then
 echo "Success"
 exit 4
else
 echo "Failed to build proof scripts..."
 echo $res
 exit 5
fi

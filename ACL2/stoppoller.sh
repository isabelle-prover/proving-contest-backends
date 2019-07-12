#!/bin/bash

PIDfile=pollerPID
PID=`cat $PIDfile`

if [ "$PID" == "-1" ]
	then
		echo "no poller is running"
	else
		echo "kill poller process (PID=$PID) now"
		sudo kill $PID
		echo "-1" > $PIDfile
fi

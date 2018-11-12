#!/bin/bash

PIDfile=serverPID
PID=`cat $PIDfile`

if [ "$PID" == "-1" ]
	then
		echo "no poller is running"
	else
		echo "kill Isabelle server process (PID=$PID) now"
		sudo kill $PID
		echo "-1" > $PIDfile
fi

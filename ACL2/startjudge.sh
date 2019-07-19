#!/bin/bash


serverPID=`cat pollerPID`

if [ "$serverPID" == "-1" ]
	then
	running=0
elif ps -p $serverPID > /dev/null
	then
	running=1
else 
	echo "-1" > serverPID
	running=0
fi

if [ "$running" == "0" ]
	then
	echo "starting poller now"

	PYTHONPATH=.. python3 poller_acl2.py DEBUG &
	pollerPID=$!
	echo "started a poller (PID=$pollerPID)"	
	echo $pollerPID > pollerPID


else
	echo "there is already a poller running (PID=$pollerPID)"		
fi

#!/bin/bash

if [ -e pythonversion ]
then
	pythonversion=`cat pythonversion`
else
	pythonversion=python3.6
fi

pollerPID=`cat pollerPID`

if [ "$pollerPID" == "-1" ]
	then
	running=0
elif ps -p $pollerPID > /dev/null
	then
	running=1
else 
	echo "-1" > serverPID
	running=0
fi

if [ "$running" == "0" ]
	then
 

	$pythonversion poller.py &
	pollerPID=$!
	echo "started an poller (PID=$pollerPID)"	
	echo $pollerPID > pollerPID

else
	echo "there is already an poller running (PID=$pollerPID)"		
fi


# --private-etc=java-8-openjdk,hosts,passwd \

#!/bin/bash

echo "======================================================"
echo "Read config"
port=`cat config | python -c 'import json,sys;obj=json.load(sys.stdin);print obj["port"];'`
echo "port = $port"
isabelleversion=`cat config | python -c 'import json,sys;obj=json.load(sys.stdin);print obj["ITP"];'` 
echo "isabelleversion = $isabelleversion"
pythonversion=`cat config | python -c 'import json,sys;obj=json.load(sys.stdin);print obj["pythonversion"];'` 
echo "pythonversion = $pythonversion"

serverPID=`cat serverPID`

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


	echo "A) Starting server for $isabelleversion" >> server.log 

	echo "===============" >> server.log 
	date >> server.log
	echo "Starting Isabelle server ($isabelleversion)" >> server.log 

	((firejail \
	  --profile=isabelle.profile \
	  --private-home=$isabelleversion.tar.gz \
	  --private-etc=java-8-openjdk,hosts,passwd \
	  --netns=isabelle-server \
		bash /var/lib/isabelle-grader/$isabelleversion/startserverscript $isabelleversion $port) 2>&1) >> server.log &
	#	 bash -c 'Isabelle2018/bin/isabelle server -n "max" -p 4711'
	serverPID=$!

	echo $serverPID > serverPID
	echo "started an Isabelle server (version=$isabelleversion) (PID=$serverPID)"		




	# update the password
	echo "B) trying to update the server password in the config (need to wait for the server to start up)"
	tries=30
	pwdupd=0
	c=1
	while [ $c -lt $tries ]
		do
		echo "$c. try:"
		./updatepassword.py
		if [ "$?" == "0" ]
			then
			c=$tries
			pwdupd=1
		else
			echo "failed, try again"
			sleep 2
			(( c++ ))
		fi
	done
	
	if [ "$pwdupd" == "0" ]
		then
		echo "failed to update password (strange :( )"
		exit 1
	fi
		






else
	echo "there is already an Isabelle server running (PID=$serverPID)"		
fi

# --private-etc=java-8-openjdk,hosts,passwd \

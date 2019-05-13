#!/bin/bash

logger="/tmp/.watchdog"

echo "===== Watchdog starts ====" >> $logger
date >> $logger
folder=`cat ~/.IsabellePoller`

echo "enter $folder" >> $logger
cd $folder

if [ -f "poller.watch" ]  
	then
	echo "found a poller.watch" >> $logger
	pw=`cat poller.watch`
	echo "content = $pw" >> $logger
	if [ $pw == "error" ] 
	then
			echo "shut down stuff" >> $logger
			./stopserver.sh >> $logger
			echo "restart stuff" >> $logger
			./startserver.sh  >> $logger
			echo "ready" > poller.watch
	fi
fi

date >> $logger
echo "===== Watchdog is done ====" >> $logger

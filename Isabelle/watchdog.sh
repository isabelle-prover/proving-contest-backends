#!/bin/bash

logger="/tmp/.watchdog$1"

echo "===== Watchdog starts ====" >> $logger
date >> $logger

folder=`cat ~/.IsabellePoller$1`

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

#!/usr/bin/python2.7
import sys
import json


if __name__ == "__main__":
	
	configfile = open("config", "r")
	cfg = configfile.read() 
	configfile.close()

	cfgData = json.loads(cfg)


	serverlog = open("server.log", "r")
	logstr = serverlog.read() 
	serverlog.close()

	logstr=logstr.split("===============")[-1]
	
	sp=logstr.split('password "')

	# the line we are looking for is not yet in the file
	if len(sp) < 2:
		sys.exit(1)

	pwd = ( sp[-1]).split('"')[0]
	print("New password is: %s" % pwd)


	cfgData["pwd"] = pwd

	configfile = open("config", "w")
	configfile.write(json.dumps(cfgData)) 
	configfile.close()

	sys.exit(0)


	

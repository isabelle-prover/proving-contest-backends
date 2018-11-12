import sys
import socket
import json

def parse(msg):
	datamsg = str(msg)
	
	pos = datamsg.find(' ')
	
	cmd=datamsg[0:pos]
	jsonmsg=datamsg[pos+1:]

	msgdict = json.loads(jsonmsg)
	
	return cmd, msgdict
	

def send(msg,socket):
	socket.sendall((msg + "\n").encode('utf-8'))
	print("sent")


def receive(socket,verbose):
	print( "start of receive")
	data = socket.recv(1024)
	if verbose: 
		print('Received', repr(data))
	if len(data)==0:
		print("Error: socket broken (receive)")
		sys.exit(-1)

	results = []
	while len(data)>0 :
		firstnl = data.find('\n')
		if firstnl < 0 :
			print( "Error: no newline found (receive)")
			sys.exit(-1)
		first = data[0:firstnl]
		data = data[firstnl+1:]
		if first.isdigit() :
			# we have a "long message"
			print( "we have a long message here")
			print( data)
			length = int(first) 
			if length <= len(data) :
				# we already have the whole message, but maybe more messages in data
				print "scanned too much!"
				results.append(data[:length])
				data=data[length:]
				#if len(data)>0 :
				#	print( "===========================================")
				#	print( "thats the rest:")
				#	print( data )
				#	print( "that was the rest:" )
			else:
				# we need to get the rest of the message
				print("need to get the rest!")
				firstpart = data
				data = ""
				#print("len so far", len(firstpart))
				#print("data so far", firstpart)
				#print("length", length)
				rest = length-len(firstpart)  
				#print("rest", rest)

				thisdata = firstpart
				# now try to get the answer
				while rest>0:
					datarest = socket.recv(rest)	
					#print("now we got this much:", len(datarest))	
					#print("now we got this:", datarest)	
					rest = rest - len(datarest)
					thisdata = thisdata + datarest
				print("final datarest len", len(thisdata))	
				print("final datarest", thisdata)		
				#print( "===========================================")
				#print( "===========================================")
				#print( "===========================================")	
				#print( "===========================================")
				if len(datarest)==0:
					print( "Error: socket broken (receive rest)")
					sys.exit(-1)
				results.append(thisdata)
		else:
			# we have a short message
			results.append(first)
	return results
 
def receiveuntildone(socket,verbose):
	databuf = []
	while True:
		if len(databuf) == 0 :
			databuf = receive(socket,verbose)
		data = databuf[0]
		databuf = databuf[1:]
		(cmd, msgdict) = parse(data)
		if cmd == "NOTE":
			print( "NOTE", msgdict)
		elif cmd == "FINISHED":
			print ("FINISHED")
			break
		elif cmd == "FAILED":
			print ("FAILED")
			break
	return (cmd, msgdict)

def twowayOK(msg,socket):
	send(msg,socket)
	data = receive(socket,True)

	print( data )

	# TODO: here we implicitely assume that we only
	#		received one message, and throw away the rest,
	#      also this answer does not carry any information, 
	#	 	it is expected to be "OK"
	return data

def twoway(msg,socket):
	send(msg,socket)
	data = receive(socket,True)

	print( data )

	# TODO: here we implicitely assume that we only
	#		received one message, and throw away the rest
	(cmd, msgdict) = parse(data[0])
	return (cmd, msgdict)


if __name__ == "__main__":
	if len(sys.argv) < 4:
		print("Unexpected number of command line arguments. Aborting!")
		sys.exit()
 	verbose=False

	password =  sys.argv[1] # "d802132e-5bf3-4df9-b90e-d50cefe0e47e"
	session = sys.argv[2]
	checkfile = sys.argv[3]
	timeout = sys.argv[4]
	#print("Hello world")
	#print(password) 

	HOST = '127.0.0.1'    # The remote host
	PORT = 4711              # The same port as used by the server
	s = socket.socket(socket.AF_INET, socket.SOCK_STREAM) 
	s.connect((HOST, PORT))
	print("connected")

	
	(cmd, msgdict) = twoway(password,s)
	
		 
	print( "result:", cmd)
	print( "version:", msgdict["isabelle_version"])

	
	print( "============== Starting Session '%s' =================" % session)

	msgbody = {"session": session}
	msg = 'session_start %s'% json.dumps(msgbody)

	(cmd, msgdict) = twoway(msg,s)

	print( "result:", cmd)
	print( "bl:", msgdict)

	(cmd, msgdict) = receiveuntildone(s,verbose)
	
	# print( msgdict)

	session_id = msgdict["session_id"]

	overallresult = 150

	if checkfile == "":
		print ("skip checking theory")
		overallresult = 3
        
	else:
		print( "============== checking theory =================")

		msgbody = {"session_id": session_id, "theories": [checkfile]}
		msg = 'use_theories %s'% json.dumps(msgbody)

		(cmd, msgdict) = twoway(msg,s)

		print( "result:", cmd)
		print("bl:", msgdict)
		print ("taskid:", msgdict["task"])

		# the checking should be finished within timeout seconds

		s.settimeout(float(timeout))
		try:
			(cmd, msgdict) = receiveuntildone(s,verbose)
			#print(msgdict)
		 
			msgout = {"msg": msgdict}

			if cmd=="FINISHED":
				print ("-----------------%s" % msgdict["ok"])
				print (type (msgdict["ok"]))
				if msgdict["ok"] :
					print("Theory checked successfully")
					overallresult = 4
				else:
					print("Theory checking finished but not 'ok'")
					overallresult = 5
			else:
				print("Theory checking failed")

		except socket.timeout as exc:
			print("Caught exception socket.timeout : %s" % exc)
			print("Theory checking failed")
			msgout = "Caught exception socket.error : %s" % exc
			overallresult = 100

			# try to cancle the task
			# this seems to break the server that's why we do
			# not cancel the task until we under stand the bug
			#s.settimeout(None)
			#print ("try to cancle task with TaskID"+ str(msgdict["task"]))
			#msgbody = {"task": msgdict["task"]}
			#msg = 'cancel %s'% json.dumps(msgbody)
			#ok = twowayOK(msg,s)
			#print ("cancelling")
			#print (ok)
			# now wait for the response
			#(cmd, msgdict) = receiveuntildone(s,verbose)
			#print ("finally:")
			#print (cmd, msgdict)

		s.settimeout(None)


		text_file = open("grader.out", "w")
		text_file.write(json.dumps(msgout))
		text_file.close()


	print("============== Stopping Session '%s' ================="%session)

	msgbody = {"session_id": session_id}
	msg = 'session_stop %s'% json.dumps(msgbody)

	(cmd, msgdict) = twoway(msg,s)

	print( "result:", cmd)
	print( "bl:", msgdict)


	(cmd, msgdict) = receiveuntildone(s,verbose)
	
	print( msgdict )

	s.close()
	sys.exit(overallresult)
	







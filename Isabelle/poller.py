import subprocess
import requests
import json
import sys
import time
import re 
import logging 
 
# logging




# XXX How about typedef and friends?
# (keyword, is_surrounded_by_whitespace)
ILLEGAL_KEYWORDS = [
	("axiomatization", True),
	("overloading", True),
	("code_printing", True),
	# XXX Can remove after checking in ML
	("translations", True),
	("declaration", False),
	# XXX Allow?
	("syntax_declaration", False),
	("oracle", False),
	("judgement", False),
	("method_setup", False),
	("simproc_setup", False),
	("SML_export", False),
	("SML_import", False),
	("SML_file", False),
	("SML_file", False),
	("ML_file", False),
	("SML_file_debug", False),
	("ML_file_debug", False),
	("SML_file_no_debug", False),
	("ML_file_no_debug", False),
	("ML", False),
	# XXX Allow the following to commands?
	("ML_val", False),
	("ML_command", False),
	("ML_prf", False),
	("setup", False),
	("local_setup", False),
	("attribute_setup", False),
	# Do we need these, i.e. can side-effects be bad?
	("parse_ast_translation", False),
	("parse_translation", False),
	("print_translation", False),
	("typed_print_translation", False),
	("print_ast_translation", False),
	("eval", "Tactic"),
	("tactic", "Tactic"),
	("raw_tactic", "Tactic")
]

ILLEGAL_SORRY = ("sorry", True)


def check_for_keyword(text, keyword_mode):
	open = re.escape("\<open>")
	old_open = re.escape("{*")
	close = re.escape("\<close>")
	old_close = re.escape("*}")
	quotation = re.escape('"')
	keyword, mode = keyword_mode
	start_regex = '(%s|\s+|\A)' % '|'.join([re.escape(')'), close, old_close, quotation])
	regex = '%s%s(\s*(%s|%s|%s))' % (start_regex, '%s', open, old_open, quotation)
	if mode == "Tactic":
		# XXX May be incomplete
		tactic_ops = [re.escape(s) for s in ['(', ',', ';', '|']]
		regex = '|'.join(tactic_ops)
		regex = '(%s)\s*%s' % (regex, '%s')
	elif mode:
		regex = '%s%s\s+' % (start_regex, '%s')

	regex = regex % keyword
	return re.search(regex, text) is not None


def check_for_keywords(prepared, allow_sorry):
	IK = ILLEGAL_KEYWORDS.copy()

	# add sorry as keyword if it is not allowed:
	if not allow_sorry:
		logger.info ("add sorry as illegal")
		IK.append(ILLEGAL_SORRY)
      
	for keyword_mode in  IK:
		if check_for_keyword(prepared, keyword_mode):
			return {"result": False, "message": "Identified illegal keyword: %s" % keyword_mode[0]}
	return {"result": True, "message": ""}

  
pollurl ="pollsubmission/?itp=ISA"
puturl ="putresult/"
rawBashCommand= 'sudo ip netns exec isabelle-server python2.7 grader.py "{0}" "{1}" "{2}" {3}' 
path="/var/lib/isabelle-grader/"


## MAIN FUNCTIONALITY
if __name__ == "__main__":
	#print(len(sys.argv))
	#if len(sys.argv) < 1:
	#	print("Unexpected number of command line arguments. Aborting!")
	#	sys.exit()

	loglevel=logging.INFO
	if len(sys.argv) > 1:
		if sys.argv[1] == "DEBUG":
			loglevel=logging.DEBUG

	## INITIALIZE LOGGING
	logging.basicConfig(filename="poller.log",
		                        filemode='a',
		                        format='%(asctime)s,%(msecs)d %(name)s %(levelname)s %(message)s',
		                        datefmt='%m-%d %H:%M:%S',
		                        level=loglevel)

	logger = logging.getLogger('poller') 

	logger.info("#####################")
	logger.info ("starting up Poller")
	logger.debug ("in debug mode")

	## READ CONFIG
	# config contains: token (to access restapi), pwd (to access Isabelle Server), 
	#					baseurl (to access restapi) )
	logger.info ("reading config")
	config= open("config", "r") 
	cnf = json.loads(config.read()) 
	config.close()
	
	pwd = cnf["pwd"]
	token = cnf["token"]
	baseurl = cnf["baseurl"]
	headers={"Content-Type": "application/json", "Authorization": "Token %s"%token}

	logger.info("pwd %s, token %s"%(pwd,token)) 


	logger.info ("entering the polling loop")
	## STARTING THE MAIN POLLING LOOP
	while True:
		time.sleep(5)

		## poll from server
		logger.debug("poll from server")


		url=baseurl+pollurl

		# send get request
		myResponse = requests.get(url, verify=True, headers=headers)
		logger.debug ("sent GET request to " + url)

		# work with answer
		if(myResponse.ok):
			jData = json.loads(myResponse.content)

			# NO TASK available
			if jData["sID"] == -1:
				logger.debug( "no submission found - sleep some time")
				time.sleep(5)

			# Got a task to grade:
			else:
				logger.info("==================================================")
				logger.info("got submission " + str(jData["sID"]) + " to grade.")

				logger.debug("The grading-task data contains {0} properties".format(len(jData)))
				logger.debug("\n")
				for key in jData:
					logger.debug( key + " : " + str(jData[key]))
				  
		
				submissionId=jData["sID"]
				assessmentId=jData["aID"]
				allow_sorry=jData["allow_sorry"]

				#### STARTING FROM HERE things get ProofAssistant-specific
				# all the necessary data is here:
				#  the submission ID:		submissionId
				#  the assessment ID:		assessmentId
				#  the defs file:			jData["files"]["Defs"]
				#  the submission file:		jData["files"]["Submission"]
				#  the check file:			jData["files"]["Check"]
				#  the image: 				jData["image"]
				#  ITP's version:			image=jData["version"]


		        # Check for illegal keywords in submission
				res = check_for_keywords(jData["files"]["Submission"], allow_sorry)
				if not res["result"]:
					grader_msg = res["message"]
					result = "0"
				else:
					# write files into shared folder with Isabelle server
					logger.debug("write the theory files")
					for thyfile in jData["files"]:
						content = jData["files"][thyfile]
						if thyfile == "Defs":
							thyfile = "Defs0" 
							p = content.split("imports",1)
							#q = p[1].split("begin",1)
							content = "theory Defs0 imports" + p[1] # q[0] + " OK_Test " + "begin" + q[1]
						logger.debug ("writing file '" + path+thyfile+".thy" + "'!")
						text_file = open(path+thyfile+".thy", "w")
						text_file.write(content)
						text_file.close()

					filename=jData["checkfile"]
					image=jData["image"]
					timeout_socket=jData["timeout_socket"]

					# check the file
					logger.info("-> Check the theories!")
					bashCommand = rawBashCommand.format(pwd,image,path+filename,timeout_socket)
					logger.info( bashCommand )

					timeout_sec = jData["timeout_all"] 
					returncode = -1
					timedout = True
					process = subprocess.Popen(bashCommand , stdout=subprocess.PIPE, shell=True)
					try:
						output, error = process.communicate(timeout=timeout_sec)
						timedout=False
						returncode = process.returncode
					except subprocess.TimeoutExpired:
						timedout=True


					if timedout:
						logger.info("the checking process was killed !!")
						returncode = 8
						grader_msg = "the checking process was killed after % s !!"%timeout_sec
					else:
						# get the return message			
						try:
							grader_output = open("grader.out", "r")
							grader_msg = grader_output.read() 
							grader_output.close()
							# invalidate grader output in order to spot bugs
							text_file = open("grader.out", "w")
							text_file.write("should be clean")
							text_file.close()
						except:
							grader_msg = "no message"

					logger.info("-> Checking is done")

					logger.info("return code is:" + str(returncode))

					

					if returncode == 4:
						# sucessfully checked
						result = "1"
					else:
						# error occured or wrong
						result = "0" 

				#### ONLY UNTIL HERE things are ProofAssistant-specific	
				# now the following data should be set in these variables
				# the score (integer 0...1 as a string): 	result
				# Id of the submission:						submissionId
				# Id of the assessment:						assessmentId
				# some message (string):					grader_msg

				data=json.dumps({'result': result, 'sID': submissionId, 'aID': assessmentId, 'msg': grader_msg})
				
				logger.debug("put the result back to the server")
				response = requests.post(baseurl+puturl,data=data, headers=headers)
		
				if(response.ok):
					jData = json.loads(response.content)
					logger.debug("The response contains {0} properties".format(len(jData)))
					logger.debug("\n")
					for key in jData:
						logger.debug(key + " : " + jData[key])
				else:
					response.raise_for_status()
				logger.info("==================================================")
		else:
			try:
				myResponse.raise_for_status()
			except requests.HTTPError as e:
				logger.debug(e)
		logger.debug("and start all over :)")




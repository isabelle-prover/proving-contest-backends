#!/usr/bin/env python3

import subprocess
import sys
import time
import re
import logging

axiom_re = re.compile("axiom ([^ ]*) .*")


if __name__ == "__main__":
	loglevel = logging.INFO

	timeout_sec = 60
	if len(sys.argv) > 1:
		timeout_sec = sys.argv[1]


	## INITIALIZE LOGGING
	logging.basicConfig(
 		#filename = "grader.log",
		stream   = sys.stderr,
		filemode = 'a',
		format   = '%(asctime)s,%(msecs)d %(name)s %(levelname)s %(message)s',
		datefmt  = '%m-%d %H:%M:%S',
		level    = loglevel)
	logger = logging.getLogger('grader')

	logger.info("## Lean Grader")
	logger.debug("In debug mode")
	logger.debug("timeout set to" + str(timeout_sec))

	lean_bin = "lean-3.4.1-linux/bin/"
	compile_command = [lean_bin + "lean", "/var/lib/lean-grader/check.lean", "-E", "/tmp/check.out", "--only-export=main_theorem"]
	check_command = [lean_bin + "leanchecker", "/tmp/check.out", "main_theorem"]


	logger.info("Compiling")
	compile_returncode = -1
	timedout = True
	process = subprocess.Popen(compile_command)
	try:
		output, error = process.communicate(timeout=timeout_sec)
		timedout = False
		compile_returncode = process.returncode
	except subprocess.TimeoutExpired:
		timedout = True

	logger.info("-> Compiling is done")
	logger.info("compiler return code is:" + str(compile_returncode))
	#logger.info("output is: "+ output)

	returncode = -1
	if(compile_returncode==0):
			
		logger.info("Checking")
		checker_result = subprocess.run(check_command, stdout=subprocess.PIPE, encoding="utf-8")
		unknown_axiom = None
		for line in checker_result.stdout.splitlines():
			m = axiom_re.match(line)
			if m and m[1] not in ["propext", "classical.choice", "quot.sound"]:
				logger.info("UNKNOWN AXIOM: " + m[1])
				unknown_axiom = m[1]

		if timedout:
			logger.info("the checking process was killed !!")
			returncode = 8
			grader_msg = "the checking process was killed after %s !!" % timeout_sec
		elif unknown_axiom:
			returncode = 8
			grader_msg = "unknown axiom %s !!" % unknown_axiom
		else :
			logger.info("successfully checked")
			# get the return message
			returncode = 4
			grader_msg = "OK"

		logger.info("-> Checking is done")

		logger.info("return code is:" + str(returncode))
	else :
		# compiling failed
		returncode = 5
	logger.info("return code is:" + str(returncode))
	
	sys.exit(returncode)
				


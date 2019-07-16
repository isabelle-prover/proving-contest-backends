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

    logger.info("## ACL2 Grader")
    logger.debug("In debug mode")
    logger.debug("timeout set to" + str(timeout_sec))

    #lean_bin = "lean-3.4.1-linux/bin/"
    #compile_command = [lean_bin + "lean", "/var/lib/lean-grader/check.lean", "-E", "/tmp/check.out", "--only-export=main_theorem"]
    #check_command = [lean_bin + "leanchecker", "/tmp/check.out", "main_theorem"]

    acl2_exec = "acl2-8.2/saved_acl2"
    acl_check_command = ["/var/lib/acl2-grader/check.sh", acl2_exec]




    logger.info("Checking")


    check_returncode = -1
    output = ""
    error = ""
    timedout = True
    process = subprocess.Popen(acl_check_command, stdout=subprocess.PIPE)
    try:
        output, error = process.communicate(timeout=timeout_sec)
        timedout = False
        check_returncode = process.returncode
    except subprocess.TimeoutExpired:
        timedout = True

    if timedout:
        logger.info("the checking process was killed !!")
        returncode = 8
        grader_msg = "the checking process was killed after %s !!" % timeout_sec
#	elif unknown_axiom:
#       returncode = 8
#       grader_msg = "unknown axiom %s !!" % unknown_axiom
    else :
        logger.info("successfully checked")
        # get the return message
        returncode = check_returncode # (either 0 = SUCCESS or 1 FAILED)
        # pass on output
        grader_msg = output

    logger.info("-> Checking is done")

    logger.info("return code is:" + str(check_returncode))

    print(grader_msg)

    sys.exit(returncode)
				


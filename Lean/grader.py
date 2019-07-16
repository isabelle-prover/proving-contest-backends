#!/usr/bin/env python3

# Return codes:
# 4: Successfully compiled and checked
# 5: Compilation failed
# 6: Timeout
# 7: Axiom/Constant found

import subprocess
import sys
import time
import re
import logging
import os

axiom_re = re.compile("\s*(axiom|constant)s?\s")
theorem_to_check = "main"
out_file = "check.out"

if __name__ == "__main__":
    loglevel = logging.INFO

    current_folder = os.path.dirname(os.path.realpath(__file__)) + "/"
    file_to_compile = current_folder + "Check.lean"
    if len(sys.argv) > 1:
        file_to_compile = sys.argv[1]
    timeout_sec = 60
    if len(sys.argv) > 2:
        timeout_sec = int(sys.argv[2])
    
    ## INITIALIZE LOGGING
    logging.basicConfig(
        #filename = "grader.log",
        stream   = sys.stderr,
        filemode = 'a',
        format   = '%(asctime)s,%(msecs)d %(name)s %(levelname)s %(message)s',
        datefmt  = '%m-%d %H:%M:%S',
        level    = loglevel
    )
    logger = logging.getLogger('grader')

    logger.info("## Lean Grader")
    logger.debug("In debug mode")
    logger.debug("timeout set to " + str(timeout_sec))

    lean_bin = current_folder + "lean/bin/"
    out_file_path = current_folder + out_file
    compile_command = [lean_bin + "lean", file_to_compile, "-E", out_file_path, "--json"]
    check_command = [lean_bin + "leanchecker", out_file_path, theorem_to_check]

    logger.info("Compiling...")
    compile_returncode = -1
    try:
        compile_result = subprocess.run(compile_command, stdout=subprocess.PIPE, timeout=timeout_sec, encoding="utf-8")
        compile_returncode = compile_result.returncode
        compile_output = compile_result.stdout
        timedout = False
        logger.info("-> Compilation done")
        logger.info("compiler return code is: " + str(compile_returncode))
        logger.info("compiler output is: " + compile_output)
    except subprocess.TimeoutExpired:
        logger.info("Compilation timeout")
        timedout = True

    returncode = -1
    if(timedout) :
        # compilation timeout
        returncode = 6
        grader_msg = "The compilation process was killed after %s seconds!" % timeout_sec
    elif (compile_returncode != 0) :
        # compilation failed
        returncode = 5
        grader_msg = compile_output
    else :
        logger.info("Checking compiled file...")
        checker_result = subprocess.run(check_command, stdout=subprocess.PIPE, timeout=timeout_sec, encoding="utf-8")
        logger.info(checker_result.stdout)
        unknown_axiom = False
        for line in checker_result.stdout.splitlines():
            m = axiom_re.match(line)
            if m :
                logger.info("found an axiom/constant")
                unknown_axiom = True
                break

        if timedout:
            logger.info("the checking process was killed !!")
            returncode = 6
            grader_msg = "the checking process was killed after %s !!" % timeout_sec
        elif unknown_axiom:
            returncode = 7
            grader_msg = "No axioms/constants allowed"
        else :
            logger.info("successfully checked")
            returncode = 4
            grader_msg = "OK"

        logger.info("-> Checking done")

    logger.info(grader_msg)
    logger.info("return code is: " + str(returncode))
    print(grader_msg)
    sys.exit(returncode)

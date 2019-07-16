#!/usr/bin/env python3

# Return codes:
SUCCESS = 0 # Successfully compiled and checked
COMPILATION_ERROR = 1
TIMEOUT = 2
AXIOM = 3

import subprocess
import sys
import time
import re
import logging
import os

LOG_LEVEL = logging.INFO

axiom_re = re.compile(".*axiom\s+([^\s][^\s:]*).*")
out_file = "check.out"

def create_axiom_output(axiom):
    return { "axiom": axiom }

if __name__ == "__main__":

    current_folder = os.path.dirname(os.path.realpath(__file__)) + "/"
    file_to_compile = current_folder + "check.lean"
    if len(sys.argv) > 1:
        file_to_compile = sys.argv[1]
    theorem_to_check = "main"
    if len(sys.argv) > 2:
        theorem_to_check = sys.argv[2]
    timeout_sec = 60
    if len(sys.argv) > 3:
        timeout_sec = int(sys.argv[3])
   
    ## INITIALIZE LOGGING
    logging.basicConfig(
        filename = current_folder + "grader.log",
        filemode = 'a',
        format   = '%(asctime)s,%(msecs)d %(name)s %(levelname)s %(message)s',
        datefmt  = '%m-%d %H:%M:%S',
        level    = LOG_LEVEL
    )
    logger = logging.getLogger('grader')

    logger.info("## Lean Grader")
    logger.debug("Timeout set to " + str(timeout_sec))

    lean_bin = current_folder + "lean/bin/"
    out_file_path = current_folder + out_file
    compile_command = [lean_bin + "lean", file_to_compile, "-E", out_file_path, "--json", "--only-export=" + theorem_to_check]
    check_command = [lean_bin + "leanchecker", out_file_path, theorem_to_check]

    logger.info("Compiling " + file_to_compile + " theorem: " + theorem_to_check + " ...")
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
        logger.info("Compilation timeout after %s seconds" % timeout_sec)
        timedout = True

    returncode = -1
    if(timedout) :
        # compilation timeout
        returncode = TIMEOUT
    elif (compile_returncode != SUCCESS) :
        # compilation failed
        returncode = COMPILATION_ERROR
        print(compile_output)
    else :
        logger.info("Checking compiled file...")
        try:
            checker_result = subprocess.run(check_command, stdout=subprocess.PIPE, timeout=timeout_sec, encoding="utf-8")
            logger.info(checker_result.stdout)
            unknown_axiom = None
            for line in checker_result.stdout.splitlines():
                match = axiom_re.match(line)
                if match and match[1] not in ["propext", "classical.choice", "quot.sound"]:
                    unknown_axiom = create_axiom_output(match[1])
                    break
        except subprocess.TimeoutExpired:
            logger.info("Checker timeout after %s seconds" % timeout_sec)
            timedout = True

        if timedout:
            returncode = TIMEOUT
        elif unknown_axiom != None:
            returncode = AXIOM
            print(unknown_axiom)
        else :
            returncode = SUCCESS

        logger.info("-> Checking done")

    sys.exit(returncode)

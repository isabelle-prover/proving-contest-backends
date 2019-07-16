import logging
import sys
import re
import codecs
import os
import subprocess
import ast

from poller import Poller, Grader_Panic 

SUCCESS = 0 # Successfully compiled and checked
COMPILATION_ERROR = 1
TIMEOUT = 2
AXIOM = 3

OK = "ok"
OK_WITH_AXIOMS = "ok_with_axioms"
ERROR = "error"

theorem_re = re.compile(".*(theorem|lemma)\s+([^\s][^\s:]*).*")

try:
    grader_folder = open("variables/grader_folder", "r").read().splitlines()[0]
except Exception as e:
    logging.exception("Cannot load grader path from variables/grader_folder")
grader_run = ["./grader_run.sh"]

def make_check_entry(name, result):
    return [ { "name": name, "result": result } ]

def make_msg_entry(where, what):
    return [ { "where": where, "what": what } ]

def make_summary(submission_is_valid, messages, checks, log=""):
    return { "submission_is_valid": submission_is_valid, "messages": messages, "checks": checks, "log": log}

def make_msg_where_string(filename, line, column):
    return filename + " at line " + str(line) + ", column " + str(column)

def make_msg_what_string(severity, text):
    return severity.upper() + ": " + text

def parse_compile_error(error, grader_path):
    # First remove the grader path from the error message
    error = error.replace(grader_path, "")
    # Then parse the string to objects and create the messages
    msgs = []
    for errorString in error.splitlines():
        try:
            error_obj = ast.literal_eval(errorString)
            msgs += make_msg_entry (
                make_msg_where_string(error_obj["file_name"], error_obj["pos_line"], error_obj["pos_col"]),
                make_msg_what_string(error_obj["severity"], error_obj["text"]))
        except BaseException: pass 
    return msgs

def parse_axiom_output(output, theorem):
    msgs = []
    try:
        obj = ast.literal_eval(output)
        msgs += make_msg_entry(theorem,
            make_msg_what_string("WARNING", "Unknown axiom '" +
            obj["axiom"] + "' used to prove theorem '" + theorem + "'."))
    except ValueError: pass
    return msgs

def get_theorem_list(file_content):
    theorems = []
    for line in file_content.splitlines():
        match = theorem_re.match(line)
        if match: theorems += [match[2]]
    return theorems

class Poller_Lean(Poller):

    def init(self):
        self.make_pollurl("LEA")

    def grade_theorem(self, theorem, summary, grader_path, timeout_all):
        logger = self.logger
        returncode = -1
        timedout = False
        try:
            lean_result = subprocess.run(grader_run + [grader_path, grader_path + "check.lean", theorem, str(timeout_all)], stdout=subprocess.PIPE, timeout=timeout_all, encoding="utf-8")
            returncode = lean_result.returncode
            output = lean_result.stdout
        except subprocess.TimeoutExpired:
            timedout = True

        if returncode == SUCCESS:
            summary["checks"] += make_check_entry(theorem, OK)
        else:
            # error occurred; compose some grader message
            summary["submission_is_valid"] = False
            if returncode == COMPILATION_ERROR:
                summary["messages"] += parse_compile_error(output, grader_path)
                summary["checks"] += make_check_entry(theorem, ERROR)
            elif returncode == TIMEOUT or timedout:
                summary["messages"] += make_msg_entry("General", "The checker timed out.")
            elif returncode == AXIOM:
                summary["messages"] += parse_axiom_output(output, theorem)
                summary["checks"] += make_check_entry(theorem, OK_WITH_AXIOMS)
            else:
                summary["messages"] += make_msg_entry("General", "Something went wrong:\n{}".format(
                    "" if output is None else str(output)))
                summary["checks"] += make_check_entry(theorem, ERROR)


    def grade_submission(self, submission_id, assessment_id, defs, submission, check, image, version,
            timeout_socket, timeout_all, allow_sorry, check_file):
        logger = self.logger
        logger.info("Grading new submission")
        logger.debug("Copying Lean files to grader folder...")
        grader_path = grader_folder + "/" + version + "/"
        for name, content in (("defs", defs), ("submission", submission), ("check", check)):
            logger.debug("writing file '{}{}.lean'!".format(grader_path, name))
            text_file = codecs.open(grader_path + name + ".lean", "w", "utf-8")
            text_file.write(content)
            text_file.close()

        logger.debug("Successfully copied submission to grader folder")
        logger.info("Compile & Check Lean proof output in container")

        summary = make_summary(True, [], [])
        for theorem in get_theorem_list(check):
            self.grade_theorem(theorem, summary, grader_path, timeout_all)

        return summary

    def tidy(self):
        pass

if __name__ == "__main__":
    loglevel = logging.INFO
    if len(sys.argv) > 1:
        if sys.argv[1] == "DEBUG":
            loglevel = logging.DEBUG

    # Initialize logging
    logging.basicConfig(
        filename="poller.log",
        filemode='a',
        format='%(asctime)s,%(msecs)d %(name)s %(levelname)s %(message)s',
        datefmt='%m-%d %H:%M:%S',
        level=loglevel
    )

    Poller_Lean().run()

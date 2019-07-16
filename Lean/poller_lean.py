import logging
import sys
import re
import codecs
import subprocess

from poller import Poller, Grader_Panic

OK = "ok"
OK_WITH_AXIOMS = "ok_with_axioms"
ERROR = "error"

try:
    grader_folder = open("variables/grader_folder", "r").read().splitlines()[0]
except Exception as e:
    logging.exception("Cannot load grader path from variables/grader_folder")
lean_compile_and_check = ["./grader.sh"]

def make_check_entry(name, result):
    return [ { "name": name, "result": result } ]

def make_grader_msg(where, what):
    return [ { "where": where, "what": what } ]

def make_summary(submission_is_valid, grader_msg, grader_checks, log):
    return { "submission_is_valid": submission_is_valid, "messages": grader_msg, "checks": grader_checks, "log": log}
      
class Poller_Lean(Poller):

    def init(self):
        self.make_pollurl("LEA")

    def grade_submission(self, submission_id, assessment_id, defs, submission, check, image, version,
            timeout_socket, timeout_all, allow_sorry, check_file):
        logger = self.logger
        logger.debug("Copy Lean files")
        grader_path = grader_folder + "/" + version + "/"
        for name, content in (("Defs", defs), ("Submission", submission), ("Check", check)):
            logger.debug("writing file '{}{}.lean'!".format(grader_path, name))
            text_file = codecs.open(grader_path + name + ".lean", "w", "utf-8")
            text_file.write(content)
            text_file.close()

        logger.info("Compile & Check Lean proof output in container")

        returncode = -1
        error = None
        try:
            lean_result = subprocess.run(lean_compile_and_check + [grader_path, grader_path + "Check.lean", str(timeout_all)], stdout=subprocess.PIPE, timeout=timeout_all, encoding="utf-8")
            returncode = lean_result.returncode
            output = lean_result.stdout
            timedout = False
        except subprocess.TimeoutExpired:
            timedout = True

        grader_msg = []
        checks = []

        if returncode == 4:
            # successfully checked
            submission_is_valid = True
            # TODO extend to multiple checks
            checks += make_check_entry("main", OK)
        else:
            # error occurred or wrong, compose some grader message
            submission_is_valid = False
            if returncode == 5:
                grader_msg += make_grader_msg("General", "" if output is None else output)
                checks += make_check_entry("main", ERROR)

            elif returncode == 6 or timedout:
                grader_msg += make_grader_msg("General", "Lean Checking timed out")
                checks += make_check_entry("main", ERROR)
            elif returncode == 7:
                grader_msg += make_grader_msg("General", "Axiom/Constant found")
                checks += make_check_entry("main", OK_WITH_AXIOMS)
            else:
                grader_msg += make_grader_msg("General", "Something went wrong. Here is some output\n{}".format(
                    "" if output is None else str(output)))
                checks += make_check_entry("main", ERROR)

        res = make_summary(submission_is_valid, grader_msg, checks, str(error))
        # print(res)
        return res

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

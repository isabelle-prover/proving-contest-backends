import logging
import sys
import re
import codecs
import subprocess

from poller import Poller, Grader_Panic

try:
    grader_folder = open("variables/grader_folder", "r").read().splitlines()[0]
except Exception as e:
    logging.exception("Cannot load grader path from variables/grader_folder")
lean_compile_and_check = ["./grader.sh"]


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
        process = subprocess.Popen(
            lean_compile_and_check + [grader_path, grader_path + "Check.lean", str(timeout_all)], stdout=subprocess.PIPE)
        try:
            output, error = process.communicate(timeout=timeout_all)
            timedout = False
            returncode = process.returncode
        except subprocess.TimeoutExpired:
            timedout = True

        grader_msg = []

        if returncode == 4:
            # successfully checked
            #grader_msg =  "OK"
            submission_is_valid = True
        else:
            # error occurred or wrong, compose some grader message
            submission_is_valid = False
            if timedout:
                grader_msg += make_grader_msg("General", "Lean Checking timed out (outer)")
            elif returncode == 5:
                grader_msg += make_grader_msg("General", "Compiling failed, message =\n{}".format(
                    "" if output is None else str(output)))
            else:
                grader_msg += make_grader_msg("General", "Something went wrong. Here is some output\n{}".format(
                    "" if output is None else str(output)))

        return make_summary(submission_is_valid, grader_msg, [], str(error))
        #  return make_summary(submission_is_valid, grader_msg, grader_checks, str(error))

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

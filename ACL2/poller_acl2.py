import logging
import sys
import re
import codecs
import subprocess

from poller import Poller, Grader_Panic

pollurl = "pollsubmission/?itp=ACL"
puturl = "putresult/"
grader_path = "/var/lib/acl2-grader/"
acl2_compile_and_check = ["./grader.sh"]
axiom_re = re.compile("axiom ([^ ]*) .*")


def make_grader_msg(where, what):
    return [ { "where": where, "what": what } ]

def make_summary(result, grader_msg, grader_checks, log):
    return { "submission_is_valid": result, "messages": grader_msg, "checks": grader_checks, "log": log}
      
class Poller_Lean(Poller):

    def init(self):
        self.make_pollurl("ACL")

    def grade_submission(self, submission_id, assessment_id, defs, submission, check, image, version, timeout_socket, timeout_all, allow_sorry, check_file):
        global grader_path, acl2_compile_and_check, axiom_re
        logger = self.logger
        logger.debug("Copy ACL2 files")

        for name, content in (("Defs", defs), ("Submission", submission), ("Check", check)):
            logger.debug("writing file '{}{}.lisp'!".format(grader_path, name))
            text_file = codecs.open(grader_path + name + ".lisp", "w", "utf-8")
            text_file.write(content)
            text_file.close()

        logger.info("Compile & Check ACL2 proof output in container")

        returncode = -1
        error = None
        process = subprocess.Popen(
            acl2_compile_and_check, stdout=subprocess.PIPE)
        try:
            output, error = process.communicate(timeout=timeout_all)
            timedout = False
            returncode = process.returncode
        except subprocess.TimeoutExpired:
            timedout = True


        logger.info("done with Compile & Check ACL2")

        grader_msg = []
        grader_checks = []
        logger.debug("returncode is %s" % returncode)
        logger.debug("output is %s" % str(output))
        logger.debug("error is %s" % str(error))

        grader_msg += make_grader_msg("General-output", str(output))

        if returncode == 4:
            # successfully checked
            #grader_msg =  "OK"
            result = True
        else:
            # error occurred or wrong, compose some grader message
            if timedout:
                grader_msg += make_grader_msg("General", "ACL2 Checking timed out (outer)")
            elif returncode == 5:
                grader_msg += make_grader_msg("General", "Compiling failed, message =\n{}".format(
                    "" if output is None else str(output)))
            else:
                grader_msg += make_grader_msg("General", "Something went wrong. Returncode {}. Here is some output\n{}".format(str(returncode),
                    "" if output is None else str(output)) )
            result = False

        return make_summary(result, grader_msg, grader_checks, str(error))

    def tidy(self):
        pass


if __name__ == "__main__":
    loglevel = logging.INFO
    if len(sys.argv) > 1:
        if sys.argv[1] == "DEBUG":
            loglevel = logging.DEBUG

    # Initialize logging
    logging.basicConfig(filename="poller.log",
                        filemode='a',
                        format='%(asctime)s,%(msecs)d %(name)s %(levelname)s %(message)s',
                        datefmt='%m-%d %H:%M:%S',
                        level=loglevel)

    Poller_Lean().run()

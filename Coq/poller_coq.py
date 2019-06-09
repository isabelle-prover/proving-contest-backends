import logging
import sys
import re
import codecs
import subprocess
import os
import shutil

from poller import Poller, Grader_Panic

script_workdir = sys.path[0]
grader_binary = os.path.join(script_workdir, "_build/default/grader/grader.exe")

class Poller_Coq(Poller):
    def init(self):
        self.make_pollurl("COQ")

    def grade_submission(self, submission_id, assesment_id, defs, submission, check, image, version, timeout_socket, timeout_all, allow_sorry, check_file):
        global grader_path
        logger = self.logger
        workdir = os.path.join(script_workdir, "grader_workdir")

        logger.debug("Copy Coq files from the submission to {}".format(workdir))

        if os.path.isdir(workdir):
            shutil.rmtree(workdir)
        os.mkdir(workdir)

        for name, content in (("Defs.v", defs), ("Submission.v", submission), ("checks.sexp", check)):
            filename = os.path.join(workdir, name)
            logger.debug("writing file '{}'".format(filename))
            file = codecs.open(filename, "w", "utf-8")
            file.write(content)
            file.close()

        logger.info("Run the Coq grader")

        process = subprocess.Popen(
            [grader_binary, "--timeout={}".format(timeout_all), workdir],
            stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True
        )
        output, error = process.communicate()
        returncode = process.returncode

        output_str = "" if output is None else str(output)
        if returncode == 0:
            grader_msg = "OK\n" + output_str
            result = "1"
        else:
            grader_msg = "There was an error or some checks failed:\n" + output_str
            result = "0"

        return result, error, [grader_msg]

    def tidy(self):
        pass


if __name__ == "__main__":
    loglevel = logging.INFO
    if len(sys.argv) > 1:
        if sys.argv[1] == "DEBUG":
            loglevel = logging.DEBUG

    Poller_Coq(loglevel).run()

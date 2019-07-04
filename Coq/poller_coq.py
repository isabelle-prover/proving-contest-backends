import logging
import sys
import re
import codecs
import subprocess
import os
import shutil
import json

from poller import Poller, Grader_Panic

script_workdir = sys.path[0]
grader_binary = os.path.join(
    script_workdir, "_build/default/grader/grader.exe")


class Poller_Coq(Poller):
    def init(self):
        self.make_pollurl("COQ")

    def grade_submission(self, submission_id, assesment_id, defs, submission, check, image, version, timeout_socket, timeout_all, allow_sorry, check_file):
        global grader_path
        logger = self.logger
        workdir = os.path.join(script_workdir, "grader_workdir")

        logger.debug(
            "Copy Coq files from the submission to {}".format(workdir))

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
            stdout=subprocess.PIPE, text=True
        )
        output, err = process.communicate()
        returncode = process.returncode

        output_str = "" if output is None else str(output)
        result_file = os.path.join(script_workdir, "result.json")

        if os.path.isfile(result_file):
            with open(result_file, 'r') as f:
                summary = json.load(f)
            summary['log'] = output_str
            if returncode != 0:
                summary['submission_is_valid'] = False
                summary['messages'].append(
                    {'where': 'global',
                     'what': 'Grader returned with a nonzero code. Please report.'}
                )
        else:
            summary = {'submission_is_valid': False,
                       'checks': [],
                       'messages': [
                           {'where': 'global',
                            'what': 'result.json not found. Please report.'}
                       ],
                       'log': output_str
            }

        return summary

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

    Poller_Coq().run()

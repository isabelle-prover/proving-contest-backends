import sys
import subprocess
import re
import logging

from poller import Poller, Grader_Panic
from grader import\
    UNKNOWN_ERROR,\
    CONNECTION_ERROR,\
    PARSE_ERROR,\
    SOCKET_TIMEOUT,\
    SOCKET_ERROR,\
    PROTOCOL_ERROR
from watchdog import Watchdog

# Return codes
CHECKING_TIMEOUT = 8

# XXX How about typedef and friends?
# (keyword, is_surrounded_by_whitespace)
ILLEGAL_KEYWORDS = [
    ("axiomatization", True),
    ("overloading", True),
    ("code_printing", True),
    # XXX Can remove after checking in ML
    ("translations", True),
    ("declaration", False),
    # XXX Allow?
    ("syntax_declaration", False),
    ("oracle", False),
    ("judgement", False),
    ("method_setup", False),
    ("simproc_setup", False),
    ("SML_export", False),
    ("SML_import", False),
    ("SML_file", False),
    ("SML_file", False),
    ("ML_file", False),
    ("SML_file_debug", False),
    ("ML_file_debug", False),
    ("SML_file_no_debug", False),
    ("ML_file_no_debug", False),
    ("ML", False),
    # XXX Allow the following to commands?
    ("ML_val", False),
    ("ML_command", False),
    ("ML_prf", False),
    ("setup", False),
    ("local_setup", False),
    ("attribute_setup", False),
    # Do we need these, i.e. can side-effects be bad?
    ("parse_ast_translation", False),
    ("parse_translation", False),
    ("print_translation", False),
    ("typed_print_translation", False),
    ("print_ast_translation", False),
    ("eval", "Tactic"),
    ("tactic", "Tactic"),
    ("raw_tactic", "Tactic")
]

ILLEGAL_SORRY = ("sorry", True)


def check_for_keyword(text, keyword_mode):
    open = re.escape("\<open>")
    old_open = re.escape("{*")
    close = re.escape("\<close>")
    old_close = re.escape("*}")
    quotation = re.escape('"')
    keyword, mode = keyword_mode
    start_regex = '(%s|\s+|\A)' % '|'.join([re.escape(')'),
                                            close, old_close, quotation])
    regex = '%s%s(\s*(%s|%s|%s))' % (start_regex,
                                     '%s', open, old_open, quotation)
    if mode == "Tactic":
        # XXX May be incomplete
        tactic_ops = [re.escape(s) for s in ['(', ',', ';', '|']]
        regex = '|'.join(tactic_ops)
        regex = '(%s)\s*%s' % (regex, '%s')
    elif mode:
        regex = '%s%s\s+' % (start_regex, '%s')

    regex = regex % keyword
    return re.search(regex, text) is not None


def check_for_keywords(prepared, allow_sorry):
    IK = ILLEGAL_KEYWORDS.copy()

    # add sorry as keyword if it is not allowed:
    if not allow_sorry:
        IK.append(ILLEGAL_SORRY)

    for keyword_mode in IK:
        if check_for_keyword(prepared, keyword_mode):
            return {"result": False, "message": "Identified illegal keyword: %s" % keyword_mode[0]}
    return {"result": True, "message": ""}


raw_bash_command = 'sudo ip netns exec isabelle-server python2.7 grader.py "{0}" "{1}" "{2}" {3}'
grader_path = "/var/lib/isabelle-grader/"


class Poller_Isa(Poller):

    def init(self):
        self.password = self.config["pwd"]
        self.logger.info("pwd {}, token {}".format(self.password, self.token))
        self.make_pollurl("ISA")

    def grade_submission(self, submission_id, assessment_id, defs, submission, check, image, version, timeout_socket, timeout_all, allow_sorry, check_file):
        global raw_bash_command, grader_path
        logger = self.logger

        # Check for illegal keywords in submission
        res = check_for_keywords(submission, allow_sorry)
        if not res["result"]:
            grader_msg = res["message"]
            result = "0"
        else:
            # write files into shared folder with Isabelle server
            logger.debug("Write the theory files")
            for name, content in (("Defs", defs), ("Submission", submission), ("Check", check)):
                if name == "Defs":
                    name = "Defs0"
                    p = content.split("imports", 1)
                    content = "theory Defs0 imports" + p[1]
                logger.debug(
                    "Writing file '{}{}.thy'!".format(grader_path, name))
                with open("{}{}.thy".format(grader_path, name), 'w') as text_file:
                    text_file.write(content)

            filename = check_file

            # check the file
            logger.info("-> Check the theories!")
            bashCommand = raw_bash_command.format(
                self.password, image, grader_path + filename, timeout_socket)
            logger.info(bashCommand)

            return_code = -1
            timedout = True
            error = None
            process = subprocess.Popen(
                bashCommand, stdout=subprocess.PIPE, stderr=subprocess.PIPE, shell=True)
            try:
                output, error = process.communicate(timeout=timeout_all)
                timedout = False
                return_code = process.returncode
            except subprocess.TimeoutExpired:
                timedout = True

            if timedout:
                logger.info("The checking process was killed")
                return_code = CHECKING_TIMEOUT
                grader_msg = "The checking process was killed after % s" % timeout_all
            else:
                # get the return message
                grader_msg = output.decode('utf-8')

            logger.info("-> Checking is done")
            logger.info("Return code is: %d" % return_code)

            if return_code == 4:
                # successfully checked
                result = "1"
            elif return_code == CONNECTION_ERROR:
                grader_msg = "Internal error: failed to connect to server"
                result = "0"
            else:
                # unknown error occurred or wrong
                result = "0"

            if "Timer already cancelled" in grader_msg:
                # signal error
                logger.info(
                    "Found error 'Timer already cancelled', signal error to watch-dog, and let it restart the Isabelle server")
                raise Grader_Panic()

            return result, error, [grader_msg]

    def tidy(self):
        pass


if __name__ == "__main__":
    loglevel = logging.INFO
    if len(sys.argv) > 1:
        if sys.argv[1] == "DEBUG":
            loglevel = logging.DEBUG

    def poll():
        Poller_Isa(loglevel).run()

    poller = Watchdog(poll, loglevel)
    poller.watch()

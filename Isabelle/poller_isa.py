import sys
import subprocess
import re
import logging
import json

from poller import Poller, Grader_Panic
from grader import\
    UNKNOWN_STATUS,\
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


raw_bash_command = 'sudo ip netns exec isabelle-server python2.7 grader.py "{0}" "{1}" "{2}" {3} {4}'
grader_path_template = "/var/lib/isabelle-grader/{0}/"


def make_grader_msg(where, what):
    return [ { "where": where, "what": what } ]

def make_summary(result, grader_msg, grader_checks, log):
    return { "submission_is_valid": result, "messages": grader_msg, "checks": grader_checks, "log": log}
      

class Poller_Isa(Poller):

    def init(self):
        self.password = self.config["pwd"]
        self.ITPshort = self.config["ITPshort"] 
        self.ITP = self.config["ITP"] 
        self.port = self.config["port"]
        self.logger.info("pwd {}, token {}, ITP {}, port {}".format(
            self.password, self.token, self.ITP, self.port))
        self.make_pollurl(self.ITPshort)



    def grade_submission(self, submission_id, assessment_id, defs, submission, check, image, version, timeout_socket, timeout_all, allow_sorry, check_file):
        global raw_bash_command, grader_path
        grader_path = grader_path_template.format(self.ITP)
        logger = self.logger

        # Check for illegal keywords in submission
        res = check_for_keywords(submission, allow_sorry)
        error = None
        grader_msg = []
        grader_checks = []

        if not res["result"]:
            grader_msg += make_grader_msg("General", res["message"])
            result = False
            logger.info("Found illegal Key Word!")
        else:
            # write files into shared folder with Isabelle server
            logger.debug("Write the theory files")
            try:
                for name, content in (("Defs", defs), ("Submission", submission), ("Check", check)):
                    if name == "Submission":
                        # this still is brittle, we hope that the first occurrence of "Defs" is th
                        # correct one, and people don't add comments before the header containing "Defs" 
                        p = content.split("Defs", 1)
                        content = p[0] + "Defs0" + p[1]
                    logger.debug(
                        "Writing file '{}{}.thy'!".format(grader_path, name))
                    with open("{}{}.thy".format(grader_path, name), 'w', encoding='utf-8') as text_file:
                        text_file.write(content)
            except Exception as e:
                return make_summary(False,
                                                make_grader_msg("Internal error",
                                                     "writing theory files failed - (%s)" % e),
                                                [], error)


            filename = check_file

            # check the file
            logger.info("-> Check the theories!")
            bashCommand = raw_bash_command.format(
                self.password, image, grader_path + filename, timeout_socket, self.port)
            logger.info(bashCommand)

            return_code = -1
            timedout = True
            process = subprocess.Popen(
                bashCommand, stdout=subprocess.PIPE, stderr=subprocess.PIPE, shell=True)
            try:
                output, error = process.communicate(timeout=timeout_all)
                error = error.decode('utf-8') 
                timedout = False
                return_code = process.returncode
            except subprocess.TimeoutExpired:
                timedout = True

            if timedout:
                logger.info("The checking process was killed")
                return_code = CHECKING_TIMEOUT
                grader_msg += make_grader_msg("General", "Checking theories takes more than %s s." % timeout_all)
            else:
                # get the return message
                returnmessage = output.decode('utf-8')            
                if "Timer already cancelled" in returnmessage:
                    # signal error
                    logger.info(
                        "Found error 'Timer already cancelled', signal error to watch-dog, and let it restart the Isabelle server")
                    raise Grader_Panic()
                # parse Isabelle Server's output
                try:
                    msgdict = json.loads(returnmessage)
                    if msgdict['msg'] and isinstance(msgdict['msg'], dict):
                        # seems to be an valid output by Isabelle Server 
                        if 'kind' in msgdict['msg'] and msgdict['msg']['kind'] == "error":
                            # we have an general error here
                            grader_msg += make_grader_msg("General", "An error occured while processing checking the Theories: (%s)" % msgdict['msg']['message']) 
                        elif 'nodes' in msgdict['msg']:
                            # we have results for specific theories, go through ...
                            for node in (msgdict['msg']['nodes']):
                                # ... each theory and ...
                                for message in node['messages']:
                                    # ... each message
                                    if message['kind'] == "error":
                                        grader_msg += make_grader_msg(node['theory_name'], message["message"])
                                    if message['message'].startswith("grading"):
                                        lines = message['message'].split("\n")[1:]
                                        splitlines = [ line.split(":") for line in lines ]
                                        for line in splitlines:
                                            res = "error"
                                            if line[1] == "passed":
                                                res = "ok"
                                            elif line[1] == "failed":
                                                res = "ok_with_axioms"
                                            grader_checks += [ {"name": line[0], "result": res } ]
                            
                except Exception as e:
                    grader_msg += make_grader_msg("Internal error", "An error occured while processing Isabelle Server's output (%s)" % e)

            logger.info("-> Checking is done")
            logger.info("Return code is: %d" % return_code)

            if return_code == 4:
                # successfully checked
                result = True
            elif return_code == CONNECTION_ERROR:
                grader_msg += make_grader_msg("Internal error", "failed to connect to server")
                result = False
            elif return_code == PARSE_ERROR:
                grader_msg += make_grader_msg("Internal error", "failed to parse server reply")
                result = False
            elif return_code == SOCKET_TIMEOUT:
                grader_msg += make_grader_msg("Internal error", "socket timeout while awaiting server reply")
                result = False
            elif return_code == SOCKET_ERROR:
                grader_msg += make_grader_msg("Internal error", "socket error while awaiting server reply")
                result = False
            elif return_code == PROTOCOL_ERROR:
                grader_msg += make_grader_msg("Internal error", "protocol error while awaiting server reply")
                result = False
            elif return_code == UNKNOWN_ERROR:
                grader_msg += make_grader_msg("Internal error", "unknown error")
                result = False
            elif return_code == UNKNOWN_STATUS:
                grader_msg += make_grader_msg("Internal error" "unknown status")
                result = False
            else:
                # unknown error occurred or wrong
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

    def poll():
        Poller_Isa().run()

    poller = Watchdog(poll)
    poller.watch()

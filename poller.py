import requests
import json
import sys
import time
import logging
from abc import ABC, abstractmethod
from watchdog import Watchdog_Restart


class Grader_Panic(Exception):
    pass


class Poller(ABC):
    def __init__(self, loglevel=logging.INFO):

        # Initialize logging
        logging.basicConfig(filename="poller.log",
                            filemode='a',
                            format='%(asctime)s,%(msecs)d %(name)s %(levelname)s %(message)s',
                            datefmt='%m-%d %H:%M:%S',
                            level=loglevel)

        logger = logging.getLogger('poller')

        logger.info("#####################")
        logger.info("starting up poller")
        logger.debug("in debug mode")

        self.logger = logger

        # Read configuration
        # config contains: token (to access restapi), pwd (to access Isabelle Server),
        #					baseurl (to access restapi) )
        logger.info("reading config")
        config = open("config", "r")
        cnf = json.loads(config.read())
        config.close()

        self.token = cnf["token"]
        self.baseurl = cnf["baseurl"]
        self.config = cnf

        # Set standard configuration
        self.pollurl_template = "pollsubmission/?itp={}"
        self.pollurl = "pollsubmission/?itp="
        self.puturl = "putresult/"
        self.itp = None
        self.headers = {"Content-Type": "application/json",
                        "Authorization": "Token {}".format(self.token)}

        # Init
        self.init()

    @abstractmethod
    def init(self):
        pass

    # Grade a submission.
    # Parameters:
    #   the submission ID:		submission_id
    #   the assessment ID:		assessment_id
    #   the defs file:			defs
    #   the submission file:	submission
    #   the check file:			check
    #   the image: 				image
    #   ITP's version:			version
    #   timeout_socket:
    #   timeout_all:
    #   Sorry allowed?:         allow_sorry
    #   Name of file to check:  check_file
    # Returns: (result, error, items)
    #   result: the score (integer 0..1 as a string) or None
    #   error:  error message or None
    #   items:  list of info messages
    @abstractmethod
    def grade_submission(self, submission_id, assessment_id, defs, submission, check, image, version, timeout_socket, timeout_all, allow_sorry=None, check_file=None):
        pass

    @abstractmethod
    def tidy(self):
        pass

    # Main loop
    def run(self):
        logger = self.logger
        logger.info("entering the polling loop")
        while True:
            time.sleep(5)
            grader_msg = ""

            # poll from server
            logger.debug("poll from server")

            url = self.baseurl + self.pollurl

            # send get request
            response = requests.get(url, verify=True, headers=self.headers)
            logger.debug("sent GET request to " + url)

            # work with answer
            if response.ok:
                data = json.loads(response.content)

                # no task available
                if data["sID"] == -1:
                    logger.debug("no submission found - sleep some time")
                    time.sleep(5)

                # got a task to grade:
                else:
                    logger.info(
                        "==================================================")
                    logger.info(
                        "got submission {} to grade.".format(data["sID"]))

                    logger.debug(
                        "The grading-task data contains {0} properties".format(len(data)))
                    logger.debug("\n")
                    for key in data:
                        logger.debug(key + " : " + str(data[key]))

                    submission_id = data["sID"]
                    assessment_id = data["aID"]
                    allow_sorry = data["allow_sorry"]

                    try:
                        result, error, items = self.grade_submission(submission_id, assessment_id, data["files"]["Defs"], data[
                            "files"]["Submission"], data["files"]["Check"], data["image"], data["version"], data["timeout_socket"],
                            data["timeout_all"], data["allow_sorry"], data["checkfile"] if "checkfile" in data else None)
                    # In case the grader signals that the watchdog should restart the whole thing.
                    except Grader_Panic:
                        self.tidy()
                        raise Watchdog_Restart()

                    data = json.dumps(
                        {'result': result, 'sID': submission_id, 'aID': assessment_id, 'msg': "\n".join(items)})

                    logger.debug("put the result back to the server")
                    response = requests.post(
                        self.baseurl + self.puturl, data=data, headers=self.headers)

                    if(response.ok):
                        data = json.loads(response.content)
                        logger.debug(
                            "The response contains {0} properties".format(len(data)))
                        logger.debug("\n")
                        for key in data:
                            logger.debug(key + " : " + data[key])
                    else:
                        response.raise_for_status()

            else:
                try:
                    response.raise_for_status()
                except requests.HTTPError as e:
                    logger.debug(e)

            logger.debug("and start all over :)")

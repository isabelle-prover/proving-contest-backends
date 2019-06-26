import sys
import socket
import json
import logging

logger = None

# Error codes
UNKNOWN_ERROR = -1
CONNECTION_ERROR = -2
PARSE_ERROR = -3
SOCKET_TIMEOUT = -4
SOCKET_ERROR = -5
PROTOCOL_ERROR = -6
UNKNOWN_STATUS = -10

# Return codes
SKIPPED_THEORY = 3
CHECKING_SUCCESS = 4
NOT_OK = 5
CHECKING_TIMEOUT = 100
ALL_GOOD = 150


class ParseError(ValueError):
    pass


class SocketBroken(Exception):
    pass


class BrokenMessage(Exception):
    pass


# Parse an Isabelle/Server message of the following format:
# CMD JSON_BODY
def parse(msg):
    data_msg = str(msg)

    pos = data_msg.find(' ')
    if pos < 0:
        raise ParseError()

    cmd = data_msg[0:pos]
    json_msg = data_msg[pos+1:]

    msgdict = json.loads(json_msg)

    return cmd, msgdict


def send(msg, socket):
    socket.sendall((msg + "\n").encode('utf-8'))
    logger.debug("Sent message via socket")


def receive(socket, verbose):
    logger.debug("Starting to receive message")
    data = socket.recv(1024)
    if verbose:
        logger.debug('Received %s' % repr(data))
    if len(data) == 0:
        logger.debug("Error: socket broken (receive)")
        raise SocketBroken("Socket broken (receive)")

    results = []
    while len(data) > 0:
        pos_newline = data.find('\n')
        if pos_newline < 0:
            logger.error("Error: no newline found (receive)")
            raise BrokenMessage("No newline found (receive)")
        first = data[0:pos_newline]
        data = data[pos_newline+1:]
        if first.isdigit():
            # we have a "long message"
            logger.debug("we have a long message here")
            logger.debug(data)
            length = int(first)
            if length <= len(data):
                # we already have the whole message, but maybe more messages in data
                logger.debug("scanned too much!")
                results.append(data[:length])
                data = data[length:]
            else:
                # we need to get the rest of the message
                logger.debug("need to get the rest!")
                first_part = data
                data = ""
                rest = length-len(first_part)

                thisdata = first_part
                # now try to get the answer
                while rest > 0:
                    datarest = socket.recv(rest)
                    rest = rest - len(datarest)
                    thisdata = thisdata + datarest
                logger.debug("final datarest len", len(thisdata))
                logger.debug("final datarest", thisdata)
                if len(datarest) == 0:
                    logger.error("Error: socket broken (receive rest)")
                    raise SocketBroken("Socket broken (receive rest)")
                results.append(thisdata)
        else:
            # we have a short message
            results.append(first)
    return results


# Receive a complete message from Isabelle/Server and parse it.
def receive_msg(socket, verbose):
    buffer = []
    while True:
        if len(buffer) == 0:
            buffer = receive(socket, verbose)
        data = buffer[0]
        buffer = buffer[1:]
        (cmd, msgdict) = parse(data)
        if cmd == "NOTE":
            logger.debug("NOTE %s" % str(msgdict))
        elif cmd == "FINISHED":
            logger.debug("FINISHED")
            break
        elif cmd == "FAILED":
            logger.debug("FAILED")
            break
    return (cmd, msgdict)


def twowayOK(msg, socket):
    send(msg, socket)
    data = receive(socket, True)

    logger.debug(data)

    # TODO: here we implicitly assume that we only
    #		received one message, and throw away the rest,
    #      also this answer does not carry any information,
    #	 	it is expected to be "OK"
    return data


def twoway(msg, socket):
    send(msg, socket)
    data = receive(socket, True)

    logger.debug(data)

    # TODO: here we implicitly assume that we only
    #		received one message, and throw away the rest
    (cmd, msgdict) = parse(data[0])
    return (cmd, msgdict)


if __name__ == "__main__":
    if len(sys.argv) < 4:
        logging.error("Unexpected number of command line arguments. Aborting!")
        sys.exit(-1)
    verbose = False

    password = sys.argv[1]  # "d802132e-5bf3-4df9-b90e-d50cefe0e47e"
    session = sys.argv[2]
    checkfile = sys.argv[3]
    timeout = sys.argv[4]

    logging.basicConfig(filename="grader.log",
                        filemode='a',
                        format='%(asctime)s,%(msecs)d %(name)s %(levelname)s %(message)s',
                        datefmt='%m-%d %H:%M:%S',
                        level=logging.INFO)
    logger = logging.getLogger('grader')

    try:
        HOST = '127.0.0.1'    # The remote host
        PORT = 4711           # The same port as used by the server
        s = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
        s.connect((HOST, PORT))
        logger.info("Connected to server")
    except Exception:
        logger.info("Error while connecting to Isabelle/Server")
        sys.exit(CONNECTION_ERROR)

    return_code = UNKNOWN_STATUS
    try:

        (cmd, msgdict) = twoway(password, s)

        logger.info("Result: %s" % cmd)
        logger.info("Version: %s" % msgdict["isabelle_version"])

        logger.info(
            "============== Starting session '%s' =================" % session)

        msgbody = {"session": session}
        msg = 'session_start %s' % json.dumps(msgbody)

        (cmd, msgdict) = twoway(msg, s)

        logger.debug("Result command: %s" % cmd)
        logger.debug("Result message: %s" % msgdict)

        (cmd, msgdict) = receive_msg(s, verbose)

        session_id = msgdict["session_id"]

        return_code = ALL_GOOD

        if checkfile == "":
            logger.info("Skip checking theory")
            return_code = SKIPPED_THEORY

        else:
            logger.info("============== Checking theory =================")

            msgbody = {"session_id": session_id, "theories": [checkfile]}
            msg = 'use_theories %s' % json.dumps(msgbody)

            (cmd, msgdict) = twoway(msg, s)

            logger.info("Checking result: %s" % cmd)
            logger.info("Checking message: %s" % msgdict)
            logger.info("Task id: %s" % msgdict["task"])

            # the checking should be finished within timeout seconds
            s.settimeout(float(timeout))
            try:
                (cmd, msgdict) = receive_msg(s, verbose)

                msgout = {"msg": msgdict}

                if cmd == "FINISHED":
                    logger.info("-----------------%s" % msgdict["ok"])
                    logger.info(type(msgdict["ok"]))
                    if msgdict["ok"]:
                        logger.info("Theory checked successfully")
                        return_code = CHECKING_SUCCESS
                    else:
                        logger.info("Theory checking finished but not 'ok'")
                        return_code = NOT_OK
                else:
                    logger.info("Theory checking failed")

            except socket.timeout as exc:
                logger.info("Caught exception socket.timeout : %s" % exc)
                logger.info("Theory checking failed")
                msgout = "Caught exception socket.error : %s" % exc
                return_code = CHECKING_TIMEOUT

            s.settimeout(None)
            print(json.dumps(msgout))

        logger.info(
            "============== Stopping session '%s' =================" % session)

        msgbody = {"session_id": session_id}
        msg = 'session_stop %s' % json.dumps(msgbody)

        (cmd, msgdict) = twoway(msg, s)

        logger.debug("Result command: %s" % cmd)
        logger.debug("Result message: %s" % msgdict)

        (cmd, msgdict) = receive_msg(s, verbose)

        logger.debug(msgdict)

    except (ParseError, json.JSONDecodeError):
        # Error while parsing message from Isabelle/Server
        return_code = PARSE_ERROR
    except BrokenMessage:
        return_code = PROTOCOL_ERROR
    except socket.timeout:
        return_code = SOCKET_TIMEOUT
    except (socket.error, SocketBroken):
        return_code = SOCKET_ERROR
    except Exception:
        # Catch all
        return_code = UNKNOWN_ERROR
    finally:
        s.close()
        sys.exit(return_code)

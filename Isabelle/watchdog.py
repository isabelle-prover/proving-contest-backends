import logging
import time


class Watchdog_Restart(Exception):
    pass


class Watchdog:
    def __init__(self, watched, loglevel=logging.INFO):
        self.watched = watched

        # Initialize logging
        logging.basicConfig(filename="watchdog.log",
                            filemode='a',
                            format='%(asctime)s,%(msecs)d %(name)s %(levelname)s %(message)s',
                            datefmt='%m-%d %H:%M:%S',
                            level=loglevel)

        logger = logging.getLogger('watchdog')

        logger.info("#####################")
        logger.info("starting up watchdog")
        logger.debug("in debug mode")

        self.logger = logger

    # Main loop
    def watch(self):
        while True:
            # wait for poller.watch to be ready
            is_ready = False
            while not is_ready:
                watch_dog = open("poller.watch", "r")
                wd = watch_dog.read().strip()
                is_ready = (wd == "ready")
                self.logger.info("waiting for poller.watch : %s (%s)" %
                            (wd, is_ready))
                watch_dog.close()
                time.sleep(5)

            try:
                self.watched()
            except Watchdog_Restart:
                self.logger.info("watch dog was instructed to restart")
                watch_dog = open("poller.watch", "w")
                watch_dog.write("error")
                watch_dog.close()

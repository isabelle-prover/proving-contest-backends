import unittest

from poller_lean import Poller_Lean

test_folder = "tests/"

class TestPoller_Lean(unittest.TestCase):
    def setUp(self):
        self.poller = Poller_Lean()

    def test_ok(self):
        with open(test_folder + "ok/Check.lean", "r") as file:
            check = file.read()
        self.poller.grade_submission(0, 0, check, check, check, 0, "3.4.2", 60, 60, None, None)

    def test_parse_error(self):
        with open(test_folder + "/parse_error/Check.lean", "r") as file:
            check = file.read()
        self.poller.grade_submission(0, 0, check, check, check, 0, "3.4.2", 60, 60, None, None)

    def test_axiom(self):
        with open(test_folder + "/axiom/Check.lean", "r") as file:
            check = file.read()
        self.poller.grade_submission(0, 0, check, check, check, 0, "3.4.2", 60, 60, None, None)

    def test_constant(self):
        with open(test_folder + "/constant/Check.lean", "r") as file:
            check = file.read()
        self.poller.grade_submission(0, 0, check, check, check, 0, "3.4.2", 60, 60, None, None)

    def test_mixed(self):
        with open(test_folder + "/mixed/Check.lean", "r") as file:
            check = file.read()
        self.poller.grade_submission(0, 0, check, check, check, 0, "3.4.2", 60, 60, None, None)

    def test_failed_proof(self):
        with open(test_folder + "/failed_proof/Check.lean", "r") as file:
            check = file.read()
        self.poller.grade_submission(0, 0, check, check, check, 0, "3.4.2", 60, 60, None, None)

    def test_sorry(self):
        with open(test_folder + "/sorry/Check.lean", "r") as file:
            check = file.read()
        self.poller.grade_submission(0, 0, check, check, check, 0, "3.4.2", 60, 60, None, None)

    def test_admit(self):
        with open(test_folder + "/admit/Check.lean", "r") as file:
            check = file.read()
        self.poller.grade_submission(0, 0, check, check, check, 0, "3.4.2", 60, 60, None, None)

if __name__ == '__main__':
    unittest.main()

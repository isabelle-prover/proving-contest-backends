import unittest

from poller_acl2 import Poller_ACL2

# CAVEAT: Occasionally, tests fail though the output is correct
# for we compare objects directly, not modulo re-ordering of arrays and members.
test_folder = "tests/"

class TestPoller_ACL2(unittest.TestCase):
    def setUp(self):
        self.poller = Poller_ACL2()
        self.maxDiff = None

    def readFile(self, path):
        with open(test_folder + path, "r") as file: return file.read()

    def runTest(self, path, expected, timeout_all=60, allow_sorry=None, check_file=None):
        defs = self.readFile(path + "/Defs.lisp")
        sub = self.readFile(path + "/Submission.lisp")
        check = self.readFile(path + "/Check-private.lisp")
        result = self.poller.grade_submission(0, 0, defs, sub, check, 0,
            "3.4.2", 60, timeout_all, allow_sorry, check_file)
        self.assertEqual(result, expected)

    def test_pyth(self):
        expected = {'submission_is_valid': True, 'messages': [{'where': 'General-output', 'what': 'b"b\'SUCCESS\\\\nCHECK-RESULT: list of pairs: ((LEMMA OK))\\\\n\'\\n"'}, {'where': 'General', 'what': 'ACL2 Checking succeed'}], 'checks': [{'name': 'LEMMA', 'result': 'ok'}], 'log': 'None'}
        self.runTest("pyth", expected)

    def test_last_theorem_skipped(self):
        print ("HALLLLLLLOOOOOOO")
        expected = {'submission_is_valid': True, 'messages': [{'where': 'General-output', 'what': 'b"b\'SUCCESS\\\\nCHECK-RESULT: list of pairs: ((TRIPLE-REV-IS-REV OK) (DOTPROD-TEST OK) (DOTPROD-REV-REV SKIPPED))\\\\n\'\\n"'}, {'where': 'General', 'what': 'ACL2 Checking succeed'}], 'checks': [{'name': 'TRIPLE-REV-IS-REV', 'result': 'ok'}, {'name': 'DOTPROD-TEST', 'result': 'ok'}, {'name': 'DOTPROD-REV-REV', 'result': 'SKIPPED'}], 'log': 'None'}
        self.runTest("last-theorem-skipped", expected)
 

if __name__ == '__main__':
    unittest.main()

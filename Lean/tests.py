import unittest

from poller_lean import Poller_Lean

# CAVEAT: Occasionally, tests fail though the output is correct
# for we compare objects directly, not modulo re-ordering of arrays and members.
test_folder = "tests/"

class TestPoller_Lean(unittest.TestCase):
    def setUp(self):
        self.poller = Poller_Lean()
        self.maxDiff = None

    def readFile(self, path):
        with open(test_folder + path, "r") as file: return file.read()

    def runTest(self, path, expected, timeout_all=60, allow_sorry=None, check_file=None):
        defs = self.readFile(path + "/defs.lean")
        sub = self.readFile(path + "/submission.lean")
        check = self.readFile(path + "/check.lean")
        self.assertEqual(self.poller.grade_submission(0, 0, defs, sub, check, 0,
            "3.4.2", 60, timeout_all, allow_sorry, check_file), expected)

    def test_ok(self):
        expected = {'submission_is_valid': True, 'messages': [], 'checks': [{'name': 'main', 'result': 'ok'}], 'log': ''}
        self.runTest("ok", expected)

    def test_axiom_unused(self):
        expected = {'submission_is_valid': True, 'messages': [], 'checks': [{'name': 'main', 'result': 'ok'}], 'log': ''}
        self.runTest("axiom_unused", expected)

    def test_axiom(self):
        expectedMsg = [{'where': 'main', 'what': "WARNING: Unknown axiom 'cheat' used to prove theorem 'main'."}]
        expected = {'submission_is_valid': True, 'messages': expectedMsg, 'checks': [{'name': 'main', 'result': 'ok_with_axioms'}], 'log': ''}
        self.runTest("axiom", expected)

    def test_axiom_ok(self):
        expected = {'submission_is_valid': True, 'messages': [], 'checks': [{'name': 'main_lemma', 'result': 'ok'}], 'log': ''}
        self.runTest("axiom_ok", expected)

    def test_constant(self):
        expectedMsg = [{'where': 'main', 'what': "WARNING: Unknown axiom 'cheat' used to prove theorem 'main'."}]
        expected = {'submission_is_valid': True, 'messages': expectedMsg, 'checks': [{'name': 'main', 'result': 'ok_with_axioms'}], 'log': ''}
        self.runTest("constant", expected)

    def test_timeout(self):
        expected = {'submission_is_valid': False, 'messages': [{'where': 'main', 'what': 'The checker timed out after 0 seconds.'}], 'checks': [{'name': 'main', 'result': 'error'}], 'log': ''}
        self.runTest("timeout", expected, 0)

    def test_parse_error(self):
        expected_msg = [{'where': 'submission.lean at line 1, column 0', 'what': "ERROR: file 'lamma' not found in the LEAN_PATH"}, {'where': 'submission.lean at line 1, column 0', 'what': "ERROR: file 'my_proof' not found in the LEAN_PATH"}, {'where': 'submission.lean at line 1, column 0', 'what': 'ERROR: invalid import: lamma\ncould not resolve import: lamma'}, {'where': 'submission.lean at line 1, column 0', 'what': 'ERROR: invalid import: my_proof\ncould not resolve import: my_proof'}, {'where': 'submission.lean at line 3, column 15', 'what': 'ERROR: command expected'}, {'where': 'check.lean at line 1, column 0', 'what': 'ERROR: invalid import: lamma\ncould not resolve import: lamma'}, {'where': 'check.lean at line 1, column 0', 'what': 'ERROR: invalid import: my_proof\ncould not resolve import: my_proof'}, {'where': 'check.lean at line 3, column 26', 'what': "ERROR: unknown identifier 'my_proof'"}, {'where': 'check.lean at line 3, column 0', 'what': "WARNING: declaration 'main' uses sorry"}, {'where': '<unknown> at line 1, column 1', 'what': 'ERROR: could not resolve import: my_proof'}]
        expected = {'submission_is_valid': False, 'messages': expected_msg, 'checks': [{'name': 'main', 'result': 'error'}], 'log': ''}
        self.runTest("parse_error", expected)

    def test_failed_proof(self):
        expectedMsg = [{'where': 'submission.lean at line 3, column 30', 'what': 'ERROR: type mismatch, term\n  or.assoc\nhas type\n  (?m_1 ∨ ?m_2) ∨ ?m_3 ↔ ?m_1 ∨ ?m_2 ∨ ?m_3\nbut is expected to have type\n  1 + 1 = 2'}, {'where': 'check.lean at line 1, column 0', 'what': "WARNING: imported file 'submission.lean' uses sorry"}]
        expected = {'submission_is_valid': False, 'messages': expectedMsg, 'checks': [{'name': 'main', 'result': 'error'}], 'log': ''}
        self.runTest("failed_proof", expected)

    def test_sorry(self):
        expected = {'submission_is_valid': True, 'messages': [{'where': 'submission.lean at line 3, column 0', 'what': "WARNING: declaration 'my_proof' uses sorry"}, {'where': 'check.lean at line 1, column 0', 'what': "WARNING: imported file 'submission.lean' uses sorry"}], 'checks': [{'name': 'main', 'result': 'ok_with_axioms'}], 'log': ''}
        self.runTest("sorry", expected)

    def test_admit(self):
        expectedMsg = [{'where': 'check.lean at line 1, column 0', 'what': "WARNING: imported file 'submission.lean' uses sorry"}, {'where': 'submission.lean at line 3, column 0', 'what': "WARNING: declaration 'my_proof' uses sorry"}]
        expected = {'submission_is_valid': True, 'messages': expectedMsg, 'checks': [{'name': 'some_lemma', 'result': 'ok_with_axioms'}], 'log': ''}
        self.runTest("admit", expected)

    def test_regex(self):
        expected = {'submission_is_valid': True, 'messages': [], 'checks': [{'name': 'main_theorem', 'result': 'ok'}], 'log': ''}
        self.runTest("regex", expected)

    def test_multiple_ok(self):
        expected = {'submission_is_valid': True, 'messages': [{'where': 'submission.lean at line 5, column 0', 'what': "WARNING: declaration 'my_proof_hard' uses sorry"}, {'where': 'check.lean at line 1, column 0', 'what': "WARNING: imported file 'submission.lean' uses sorry"}, {'where': 'proof_cheat', 'what': "WARNING: Unknown axiom 'cheat' used to prove theorem 'proof_cheat'."}], 'checks': [{'name': 'proof_easy', 'result': 'ok'}, {'name': 'proof_hard', 'result': 'ok_with_axioms'}, {'name': 'proof_cheat', 'result': 'ok_with_axioms'}], 'log': ''}
        self.runTest("multiple_ok", expected)

if __name__ == '__main__':
    unittest.main()

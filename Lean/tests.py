import unittest

from poller_lean import Poller_Lean

test_folder = "test/"

class TestPoller_Lean(unittest.TestCase):
    def setUp(self):
        self.poller = Poller_Lean()
        self.maxDiff = None
        self.leanVersion = self.readFile("variables/lean_version").splitlines()[0]

    def readFile(self, path):
        with open(path, "r", encoding="utf-8") as file: return file.read()

    def readTest(self, path):
        return self.readFile(test_folder + path)

    def runTest(self, path, expected, timeout_all=60, allow_sorry=None, check_file=None):
        defs = self.readTest(path + "/defs.lean")
        sub = self.readTest(path + "/submission.lean")
        check = self.readTest(path + "/check.lean")
        result = self.poller.grade_submission(0, 0, defs, sub, check, 0,
            self.leanVersion, 60, timeout_all, allow_sorry, check_file)
        result['messages'] = sorted(list(m.items()) for m in result['messages'])
        expected['messages'] = sorted(list(m.items()) for m in expected['messages'])
        self.assertDictEqual(expected, result)

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

    def test_axiom2(self):
        #  Optimally, this should say '«quot.sound : a»', but the leanchecker cuts of everything following the colon
        expectedMsg = [{'where': 'main', 'what': "WARNING: Unknown axiom '«quot.sound»' used to prove theorem 'main'."}]
        expected = {'submission_is_valid': True, 'messages': expectedMsg, 'checks': [{'name': 'main', 'result': 'ok_with_axioms'}], 'log': ''}
        self.runTest("axiom2", expected)

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
        expected_msg = [{'where': 'check.lean at line 3, column 0', 'what': "WARNING: declaration 'main' uses sorry"}, {'where': 'check.lean at line 3, column 26', 'what': "ERROR: unknown identifier 'my_proof'"}, {'where': 'submission.lean at line 3, column 0', 'what': 'ERROR: command expected'}]
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

    def test_notation_cheat(self):
        expected = {'submission_is_valid': False, 'messages': [{'where': 'check.lean at line 4, column 23', 'what': 'ERROR: ambiguous overload, possible interpretations\n  0 = 0\n  false\nAdditional information:\ncheck.lean:4:23: context: switched to basic overload resolution where arguments are elaborated without any information about the expected type because expected type was not available'}], 'checks': [{'name': 'you_broke_it', 'result': 'error'}], 'log': ''}
        self.runTest("notation_cheat", expected)

    def test_local_notation(self):
        expected = {'submission_is_valid': False, 'messages': [{'where': 'check.lean at line 3, column 32', 'what': 'ERROR: type mismatch, term\n  soundness_bug\nhas type\n  true\nbut is expected to have type\n  false'}], 'checks': [{'name': 'you_broke_it', 'result': 'error'}], 'log': ''}
        self.runTest("local_notation", expected)

    def test_mathlib(self):
        expected = {'submission_is_valid': True, 'messages': [], 'checks': [{'name': 'main', 'result': 'ok'}, {'name': 'main2', 'result': 'ok'}], 'log': ''}
        self.runTest("mathlib", expected)

    def test_noncomputable(self):
        expectedMsg = [{'where': 'check.lean at line 4, column 4', 'what': "ERROR: definition 'computable' is noncomputable, it depends on 'my_int_of_nat'"}]
        expected = {'submission_is_valid': False, 'messages': expectedMsg, 'checks': [{'name': 'correctness', 'result': 'error'}], 'log': ''}
        self.runTest("noncomputable", expected)

    def test_computable(self):
        expected = {'submission_is_valid': True, 'messages': [], 'checks': [{'name': 'correctness', 'result': 'ok'}], 'log': ''}
        self.runTest("computable", expected)

if __name__ == '__main__':
    unittest.main()

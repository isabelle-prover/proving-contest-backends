# Setup

## First Time
Run `preparejudge.sh`. The script installs a grader compatible with the lean version specified in `variables/lean_version` to the path specified in `variables/grader_folder/${lean_version}`.

Before running the first time, you need to copy `config.tmp` to `config`.
Then insert the correct URL for the frontend server and your access token.

## Start the judge
The backend can simply be administered via
`./judge start`, `./judge status`, and `./judge stop`.

It expects the following structure of the submitted files:

+-- _defs.lean_
+-- _submission.lean_
+-- _check.lean_

The poller checks all lemmas/theorems in `check.lean`. 

## Tests
Tests can be executed using `tests_run.sh` and `tests.py`.

## TODOs
- firejail needs to be fixed in `grader_run.sh`
- Mathlib is not used by the grader.
- The lean version is strict at the moment, for example, a server running Lean 3.4.2 will not accept request for Lean 3.4.1.
- The passed `timeout_all` flag is used on a per theorem basis (but should be on a per submission basis).
- Some of the tests might fail though the output is correct for we compare objects directly, not modulo re-ordering of arrays and members.

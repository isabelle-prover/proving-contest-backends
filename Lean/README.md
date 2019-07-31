# Setup

## First Time
1. Run `preparejudge.sh`. The script installs a grader compatible with the Lean version specified in `variables/lean_version` and pre-compiled mathlib version specified in `variables/mathlib_version` to the path specified in `variables/grader_folder`.
2. Before running the poller, you need to copy `config.tmp` to `config`.
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
- The lean version is strict at the moment, for example, a server running Lean 3.4.2 will not accept request for Lean 3.4.1.
- The passed `timeout_all` flag is used on a per theorem basis (but should be on a per submission basis).
- Only one mathlib version at a time is supported now (image field (or similar hints) are not used by the poller atm)

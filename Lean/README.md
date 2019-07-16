# Setup

## First Time
Run `preparejudge.sh`. The script installs a grader compatible with the lean version specified in `variables/lean_version` to the path specified in `variables/grader_folder/${lean_version}`.

Before running the first time, you need to copy `config.tmp` to `config`.
Then insert the correct URL for the frontend server and your access token.

## Start the judge
The backend can simply be administered via
`./judge start`, `./judge status`, and `./judge stop`.

At the moment, the grader checks the lemma/theorem called `main` in `Check.lean`.

## Tests
Tests can be executed using `tests_run.sh` and `tests.py`.

## TODOs
- Messages returned from `grader.py` to `poller_lean.py` needs to be enhanced (better (error) messages).
- Fundamentally, check messages seem to work, but that should be double checked.
- Variables are not detected
- The grader can only check one theorem at a time (`main`)
- `sorry`/`admit` stops the compilation process. This causes problems if multiple lemmas should be checked from the same submission (cf. previous point)
- firejail needs to be fixed in `grader.sh`

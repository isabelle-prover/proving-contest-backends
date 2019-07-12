# Setup

The only assumption on your installation is that the Lean binaries can be found in the folder
`lean-3.4.1-linux/bin/`. This should also work for newer versions of lean.
To change the path for the binaries, you can modify the variable `lean_bin`
in `grader.py`.

Before running the first time, you need to copy `config.tmp` to `config`.
Then insert the correct URL for the frontend server and your access token.

Now, the backend can simply be administered via
`./judge start`, `./judge status`, and `./judge stop`.
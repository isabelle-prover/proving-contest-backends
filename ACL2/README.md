# Setup

The only assumption on your installation is that acl2 8.2 is installed and the binary can be found in folder `acl2-8.2/saved_acl2`.

Before running the first time, you need to copy `config.tmp` to `config`.
Then insert the correct URL for the frontend server and your access token.

Before the first start, prepare the server with `sudo ./judge prepare`

Now, the backend can simply be administered via
`./judge start`, `./judge status`, and `./judge stop`.

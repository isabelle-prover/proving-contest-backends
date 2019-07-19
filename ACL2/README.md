# Setup

m4 must be installed:
> sudo apt-get install m4

The only assumption on your installation is that acl2 8.2 is installed and the binary can be found in folder `acl2-8.2/saved_acl2`.

one can also install acl2-8.2 with the prepare script:
> ./judge prepare


Before running the first time, you need to copy `config.tmp` to `config`.
Then insert the correct URL for the frontend server and your access token.

Before the first start, prepare the server with `sudo ./judge prepare`

Now, the backend can simply be administered via
`./judge start`, `./judge status`, and `./judge stop`.

# Coq grader

## Initial setup

You need to have [opam](https://opam.ocaml.org/) >= 2.0 installed.

Then run `./prepare.sh` to create a local opam switch with everything necessary
installed (this will take some time).

### Troubleshooting

If the opam invocation fails for some reason: after you fix the cause of the
issue, either remove the `_opam` repository and re-run the `prepare.sh` script
(this will redo everything), or do `eval $(opam env)` and then `opam install -y
--deps-only .` (this will continue from where it failed).

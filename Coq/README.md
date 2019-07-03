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

## Running the grader

Use `./judge start` to run the grader (in the background), and `./judge stop` to
stop it.

## Syntax of the check files

A `checks.sexp` file consists of a list of statements, in s-expression syntax,
that are either:

- `(Check "thm_name" "theorem type")`

  This will check that a theorem has the expected type. This will be done in an
  environment corresponding to running `Require Import Defs. Require
  Submission.`. In particular this means that names from the submission must be
  qualified (e.g `Submission.the_name`).

  This will also check that the user theorem does not rely on unwanted axioms.

- `(Check_refl "statement")`

  Checks that the given statement holds by reflexivity (useful to test that user
  definitions satisfy basic computational properties).

- `(Allow_axioms (Coq.Logic.Classical_Prop.classic ...))`

  Allow some axioms in the rest of the file. The axiom names must be fully
  qualified.


**NB**: The syntax of strings in s-expressions follow the OCaml conventions. In
particular, this means that characters such as `\` or `"` must be properly
escaped (as `\\` and `\"`).


For some simple examples, see [grader/workdir](grader/workdir).

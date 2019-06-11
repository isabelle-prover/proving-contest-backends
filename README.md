# proving-contest-backends
This repository containts implementations of backends for the proving contest system `competitions.isabelle.systems` for several theorem provers.

## How To Get Started
Setup is slightly different for each of the provers but the general idea is to handle administration
of the prover backends via the `judge` scripts after some initial setup.
The individual steps for initial setup are documented in the `README` files of the subfolders corresponding to the different provers.

## Implementing Your Own Backend
The file `poller.py` handles the communication with the frontend server.
It provides an abstract class `Poller` in which mainly the method `grade_submission` needs to be implemented.
For a simple example, see the Lean implementaion in `Lean/lean_poller.py`.
Sometimes, a watchdog facility to restart everything in case of an error
can be useful. This functionality is implemented in in `watchdog.py`.
See the Isabelle implementation for a usage example.

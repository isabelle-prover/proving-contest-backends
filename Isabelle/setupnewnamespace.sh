#!/bin/bash



ip netns add isabelle-server
ip netns exec isabelle-server ip link set lo up

# start script now:
# sudo ip netns exec isabelle-server python grader.py ""


#!/bin/bash

# Parameters:
# $1 path to the grader folder containing grader.py. Default: Constructed from variables/lean_version and variables/grader_folder
# $2 path of the file that should be checked. Default: ${grader_path}Check.lean
# $3 name of the theorem that should be checked. Default: main
# $4 timeout for the grader. Default: 60 (seconds)

lean_version=`cat variables/lean_version`
grader_path=`cat variables/grader_folder`/$lean_version/
actual_path=${1:-$grader_path}

#TODO make firejail work again
# firejail \
    # --profile=lean.profile \
    # --private=$actual_path \
    python3 "${actual_path}grader.py" "${2:-${actual_path}Check.lean}" ${3:-main} ${4:-60}

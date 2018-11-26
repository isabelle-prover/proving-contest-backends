#!/bin/bash


	firejail \
	  --profile=lean.profile \
	  --private-home=lean-3.4.1-linux \
		python3 /var/lib/lean-grader/grader.py 2>> grader.out

#!/bin/bash

leansource="https://github.com/leanprover/lean/releases/download/v3.4.1/lean-3.4.1-linux.tar.gz"
leanversion="lean-3.4.1-linux"
graderfolder=/var/lib/lean-grader
currentfolder=`pwd`

sudo mkdir -p $graderfolder
sudo chown $USER $graderfolder
sudo chmod 777 $graderfolder


echo "======================================================"
echo "Installing Lean" 
if [ -d "$HOME/$leanversion" ]
then
	echo "lean already exists"
else
	cd /tmp
	wget $leansource
	tar -xzf lean-3.4.1-linux.tar.gz -C ~
	cd $currentfolder
fi

echo "======================================================"
echo "copying files to shared folder"
cp "grader.py" $graderfolder
 

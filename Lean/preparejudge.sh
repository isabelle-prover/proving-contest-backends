#!/bin/bash

lean_version=`cat variables/lean_version`
lean_file="lean-$lean_version-linux.tar.gz"
lean_source="https://github.com/leanprover/lean/releases/download/v$lean_version/$lean_file"
install_folder=`cat variables/grader_folder`/$lean_version
current_folder=`pwd`

sudo mkdir -p $install_folder
sudo chown $USER $install_folder
sudo chmod 777 $install_folder

echo "======================================================"
echo "Installing Lean $lean_version" 
if [ -d "$install_folder/lean" ]
then
	echo "Lean already exists at $install_folder/lean"
else
	cd /tmp
	wget $lean_source
	tar -xzf $lean_file -C $install_folder && mv "$install_folder/lean-$lean_version-linux" "$install_folder/lean"
	cd $current_folder
fi
echo "Lean $lean_version installed at $install_folder/lean"
echo "======================================================"
echo "copying grader file to grading folder $install_folder"
cp "grader.py" $install_folder
 

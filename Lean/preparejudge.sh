#!/bin/bash

lean_version=`cat variables/lean_version`
lean_file="lean-$lean_version-linux.tar.gz"
lean_source="https://github.com/leanprover/lean/releases/download/v$lean_version/$lean_file"
lean_folder="lean"

mathlib_version=`cat variables/mathlib_version`
mathlib_file="mathlib-olean-nightly-$mathlib_version.tar.gz"
mathlib_source="https://github.com/leanprover-community/mathlib-nightly/releases/download/nightly-$mathlib_version/$mathlib_file"
mathlib_folder="mathlib"
# TODO future extension: allow multiple mathlib versions by using version specific folder
# mathlib_folder="mathlib-$mathlib_version"

install_folder=`cat variables/grader_folder`/$lean_version
current_folder=`pwd`

sudo mkdir -p "$install_folder"
sudo chown $USER "$install_folder"
sudo chmod 777 "$install_folder"

cd /tmp
echo "======================================================"
echo "Installing Lean $lean_version" 
if [ -d "$install_folder/$lean_folder" ]
then
    echo "Lean already exists at $install_folder/$lean_folder"
else
    echo "Downloading Lean..."
    wget -N "$lean_source"
    echo "Done downloading Lean. Exctracing Lean..."
    tar -xzf "$lean_file" -C "$install_folder" && mv "$install_folder/lean-$lean_version-linux" "$install_folder/$lean_folder"
    echo "Done exctracing Lean."
fi
if [ -d "$install_folder/$mathlib_folder" ]
then
    echo "Mathlib already exists at $install_folder/$mathlib_folder"
else
    echo "Downloading mathlib..."
    wget -N "$mathlib_source"
    echo "Done downloading mathlib. Exctracing mathlib files..."
    tar -xzf "$mathlib_file" -C "$install_folder" && mv "$install_folder/src" "$install_folder/$mathlib_folder"
    echo "Done extracting mathlib."
fi
cd "$current_folder"

echo "Lean $lean_version installed at $install_folder/$lean_folder"
echo "Mathlib-$mathlib_version installed at $install_folder/$mathlib_folder"
echo "======================================================"
echo "copying grader file to grading folder $install_folder"
cp "grader.py" $install_folder
 

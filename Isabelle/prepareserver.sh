#!/bin/bash

echo "======================================================"
echo "Read config"
port=`cat config | python -c 'import json,sys;obj=json.load(sys.stdin);print obj["port"];'`
echo "port = $port"
isabelleversion=`cat config | python -c 'import json,sys;obj=json.load(sys.stdin);print obj["ITP"];'` 
echo "isabelleversion = $isabelleversion"
sessions=`cat config | python -c 'import json,sys;obj=json.load(sys.stdin);print("\n".join([session for session in obj["sessions"]]));'`
echo "sessions = $sessions"


settingsfile="settings$isabelleversion"
graderfolder=/var/lib/isabelle-grader/$isabelleversion
mkdir -p $graderfolder

isapref=$graderfolder/.isabelle/$isabelleversion
echo "======================================================"
echo "prepare isabelle preferences in: $isapref"
mkdir -p "$isapref/etc"
mkdir -p "$isapref/heaps"
cp $settingsfile "$isapref/etc/settings"


echo "======================================================"
echo "Now copying setting to local ~/.isabelle/$isabelleversion/etc/settings"
backup=0
if [ -e ~/.isabelle/$isabelleversion/etc/settings ]
then
    echo "backup local settings to '/tmp/$isabelleversion/etc/settings'"
    mkdir -p "/tmp/$isabelleversion/etc"
    cp ~/.isabelle/$isabelleversion/etc/settings /tmp/$isabelleversion/etc/settings
    backup="1"
fi


echo "copy custom settings to '~/.isabelle/$isabelleversion/etc/settings'"
mkdir -p ~/.isabelle/$isabelleversion/etc
cp $settingsfile ~/.isabelle/$isabelleversion/etc/settings

 
echo "======================================================"
echo "build sessions specified in: $sessions"
for sn in $sessions; do
 echo "---- build $sn -----"
 ~/$isabelleversion/bin/isabelle build -b $sn; 
done 


if [ "$isabelleversion" = "Isabelle2018" ];
then
      
    echo "======================================================"
    echo "build extra session IMP for Semantics"

    folder=`pwd`
    echo "entering $graderfolder"
    cd $graderfolder
    echo "cloning repository"
    git clone https://bitbucket.org/plammich/semantics1819_public.git
    cd semantics1819_public
    git pull
    echo "building IMP"
    ~/$isabelleversion/bin/isabelle build -b -d . "IMP"; 
    echo "building IMP2"
    ~/$isabelleversion/bin/isabelle build -b -d . "IMP2"; 
     
    echo "$graderfolder/semantics1819_public" > $graderfolder/.isabelle/$isabelleversion/ROOTS

    echo "leavin $graderfolder"
    echo "entering $folder"
    cd $folder
fi


if [ "$backup" = "1" ]   
then 
    echo "======================================================"
    echo "restore '~/.isabelle/$isabelleversion/etc/settings'"
    cp /tmp/$isabelleversion/etc/settings ~/.isabelle/$isabelleversion/etc/settings
fi 

echo "======================================================"
echo "copy heaps"
cp -R ~/.isabelle/$isabelleversion/heaps $isapref

echo "======================================================"
echo "copy startserverscript"
cp -R startserverscript $graderfolder


echo "======================================================"
echo "prepare checking files in folder: $graderfolder"
cp OK_Test.thy $graderfolder
cp Defs.thy $graderfolder



echo "======================================================"
echo "setup new network namespace"
./setupnewnamespace.sh

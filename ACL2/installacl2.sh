#!/bin/sh

currdirr=`pwd`

installpath=$1

if [ -d "$1/acl2-8.2" ]; then
    echo "folder '$1/acl2-8.2' already exists!"
    exit 1
fi

echo "getting ACL2"

mkdir -p $1
cd $1

wget https://github.com/acl2-devel/acl2-devel/releases/download/8.2/acl2-8.2.tar.gz
tar xfz acl2-8.2.tar.gz

ACLfolder="$1/acl2-8.2"

echo "installing CCL"

cd /tmp


mkdir cclinstall
cd cclinstall
git clone https://github.com/Clozure/ccl
cd ccl

cclversion=`git rev-parse HEAD | tail -c 10`
today=`date +'%Y-%m-%d'`
foldername="$today$cclversion"
echo $foldername
cd ../

echo "
#!/bin/sh

export CCL_DEFAULT_DIRECTORY=$ACLfolder/lisps/ccl/$foldername/ccl
\${CCL_DEFAULT_DIRECTORY}/scripts/ccl64 \"\$@\"" > ccl.sh

chmod +x ccl.sh

cd ../
mv cclinstall "$foldername"
cd "$foldername/ccl"


wget https://github.com/Clozure/ccl/releases/download/v1.12-dev.5/linuxx86.tar.gz
tar xfz linuxx86.tar.gz
echo "(rebuild-ccl :full t)\n(quit)" | ./lx86cl64 
echo "(rebuild-ccl :full t)\n(quit)" | ./lx86cl64 
 
cd ../..
mkdir -p "$ACLfolder/lisps/ccl"
mv $foldername "$ACLfolder/lisps/ccl"


echo "installing ACL2"
cd "$ACLfolder"
make LISP="$ACLfolder/lisps/ccl/$foldername/ccl.sh"
make basic



echo "getting out of here"
cd $currdirr


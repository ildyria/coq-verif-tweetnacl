#!/bin/sh

cd c

# generate the .v file of TweetnaclVerifiableC.c
clightgen -normalize tweetnaclVerifiableC.c

# set the proper path to compcert library
sed -i 's/^Require Import/From compcert.exportclight Require Import/' tweetnaclVerifiableC.v

cd ..

# remove _CoqProject if it alreqdy exists
[ -e _CoqProject ] && rm _CoqProject

# generate the path for coqide and coqv
for D in */; do
	echo $D | sed 's/.$//' | echo "-R $(cat -) Tweetnacl_verif" >> _CoqProject
done

# generate the list of files for coq_makefile
ls */*.v >> _CoqProject

coq_makefile INSTALLDEFAULTROOT = Tweetnacl_verif -f _CoqProject -o Makefile

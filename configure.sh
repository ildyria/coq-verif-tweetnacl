#!/bin/sh

# remove _CoqProject if it alreqdy exists
[ -e _CoqProject ] && rm _CoqProject

# generate the path for coqide and voqv
for D in $(find * -maxdepth 1 -type d | egrep -v '^C|^slides|^readings'); do
	echo "-Q $D Tweetnacl.$D" >> _CoqProject
done

echo "" >> _CoqProject

# generate the list of files for coq_makefile
ls */*.v | egrep -v '^C/' >> _CoqProject

coq_makefile INSTALLDEFAULTROOT = Tweetnacl -f _CoqProject -o Makefile
# coq_makefile -f _CoqProject -o Makefile


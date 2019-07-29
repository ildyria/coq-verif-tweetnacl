#!/bin/sh

# remove _CoqProject if it already exists
[ -e _CoqProject ] && rm _CoqProject

# generate the path for coqide and voqv
for D in $(find * -maxdepth 1 -type d); do
	echo "-Q $D Tweetnacl.$D" | sed 's/\//./2'>> _CoqProject
done

echo "" >> _CoqProject

# generate the list of files for coq_makefile
find * -name "*.v" -print >> _CoqProject

coq_makefile INSTALLDEFAULTROOT = Tweetnacl -f _CoqProject -o Makefile

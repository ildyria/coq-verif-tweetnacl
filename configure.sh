#!/bin/sh

# remove _CoqProject if it alreqdy exists
[ -e _CoqProject ] && rm _CoqProject

while : ; do
	case "$1" in
	"")
		break;;
	--no-High|--no-high)
		nohigh=true; shift;;
	esac
done

if test "$nohigh" = "true"; then
	echo "no-high"
	filt='^C|^slides|^readings|^High'
else
	filt='^C|^slides|^readings'
fi

# generate the path for coqide and voqv
for D in $(find * -maxdepth 1 -type d | egrep -v $filt); do
	echo "-Q $D Tweetnacl.$D" >> _CoqProject
done

echo "" >> _CoqProject

# generate the list of files for coq_makefile
ls */*.v | egrep -v $filt >> _CoqProject


coq_makefile INSTALLDEFAULTROOT = Tweetnacl -f _CoqProject -o Makefile
# coq_makefile -f _CoqProject -o Makefile


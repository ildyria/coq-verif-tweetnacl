all: tweetverif.pdf csf-supplementary/previous.pdf

SOURCES= code-tweetnacl.tex collection.bib conclusion.tex coq.tex highlevel.tex intro.tex lowlevel.tex preliminaries.tex proofs.tex rfc.tex t.bib tweetverif.tex tweetnacl.diff

tweetverif.pdf: $(SOURCES)
	pdflatex tweetverif.tex
	bibtex tweetverif
	pdflatex tweetverif.tex
	pdflatex tweetverif.tex

csf-supplementary/previous.pdf:
	make -C csf-supplementary

tweetnacl.diff:
	@echo $(BOLD)$(YELLOW)"Generating tweetnacl.diff"$(NO_COLOR)$(DARKGRAY)
	diff -u ../proofs/vst/c/tweetnacl.c ../proofs/vst/c/tweetnaclVerifiableC.c > tweetnacl.diff.tmp; [ $$? -eq 1 ]
	sed -i -e 1,2d tweetnacl.diff.tmp
	echo '--- tweetnacl.c' >> tweetnacl.diff
	echo '+++ tweetnaclVerifiableC.c' >> tweetnacl.diff
	cat tweetnacl.diff.tmp >> tweetnacl.diff
	rm tweetnacl.diff.tmp


.PHONY: clean

clean:
	-rm tweetverif.aux
	-rm tweetverif.log
	-rm tweetverif.out
	-rm tweetverif.pdf
	-rm tweetverif.thm
	-rm tweetverif.bbl
	-rm tweetverif.blg
	-rm tweetverif.brf
	make -C csf-supplementary clean

SOURCES= code-tweetnacl.tex collection.bib conclusion.tex coq.tex highlevel.tex intro.tex lowlevel.tex preliminaries.tex proofs.tex rfc.tex t.bib tweetverif.tex

tweetverif.pdf: ${SOURCES}
	pdflatex tweetverif.tex
	bibtex tweetverif
	pdflatex tweetverif.tex
	pdflatex tweetverif.tex

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

LATEXMK = ./latexrun.py
READ = evince
SOURCES := $(wildcard *.tex)
DEPS := $(wildcard *.sty) ECC101/frame.tex
PDFS := $(notdir $(SOURCES:.tex=.pdf))


all: $(PDFS)

cleanpdf:
	@rm *.pdf 2> /dev/null || true

force: cleanpdf $(PDFS)

%.pdf: %.tex $(DEPS)
	echo $*.tex
	$(LATEXMK) $*.tex

open:
	${READ} $(PDFS)

clean:
	@echo cleaning...
	@rm -fr latex.out 2> /dev/null || true

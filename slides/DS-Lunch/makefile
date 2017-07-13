LATEXMK = latexmk -pdf
LATEX = pdflatex
READ = evince
SOURCES := $(wildcard *.tex)
PDFS := $(notdir $(SOURCES:.tex=.pdf))
PNGS := $(notdir $(SOURCES:.tex=.png))


all: $(PDFS)

cleanpdf:
	@rm png/*.png 2> /dev/null || true
	@rm *.pdf 2> /dev/null || true

force: cleanpdf $(PDFS)

%.pdf: %.tex
	echo $*.tex
	$(LATEXMK) $*.tex

open:
	${READ} $(PDFS)


clean:
	@echo cleaning...
	@rm *.aux 2> /dev/null || true
	@rm *.log 2> /dev/null || true
	@rm *.out 2> /dev/null || true
	@rm *.toc 2> /dev/null || true
	@rm *.snm 2> /dev/null || true
	@rm *.nav 2> /dev/null || true
	@rm *.vrb 2> /dev/null || true
	@rm *.bbl 2> /dev/null || true
	@rm *.blg 2> /dev/null || true
	@rm *.idx 2> /dev/null || true
	@rm *.lol 2> /dev/null || true
	@rm *.fls 2> /dev/null || true
	@rm *.fdb_latexmk 2> /dev/null || true

png: $(PDFS) $(PNGS)

%.png: %.pdf
	convert -density 300 $*.pdf -quality 90 $*.png

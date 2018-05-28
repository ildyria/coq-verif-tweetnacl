FILES := $(wildcard *.tex) $(wildcard tikz/*.tex) $(wildcard *.sty)

curve25519.pdf: FORCE $(FILES) collection.bib
	./latexrun.py curve25519.tex

depend:
		@echo $(FILES)

.PHONY: clean FORCE

clean:
	@echo cleaning...
	@rm *.pdf 2> /dev/null || true
	@rm *.aux 2> /dev/null || true
	@rm *.bbl 2> /dev/null || true
	@rm *.blg 2> /dev/null || true
	@rm *.brf 2> /dev/null || true
	@rm *.dvi 2> /dev/null || true
	@rm *.fdb_latexmk 2> /dev/null || true
	@rm *.fls 2> /dev/null || true
	@rm *.log 2> /dev/null || true
	@rm *.out 2> /dev/null || true
	@rm */*.aux 2> /dev/null || true

TEX := $(filter-out tweetverif.tex,$(wildcard *.tex))
FILES := $(TEX) $(wildcard tikz/*.tex) $(wildcard *.sty)

tweetverif.pdf: FORCE tweetverif.tex
	python3 latexrun.py tweetverif.tex

tweetverif.tex: FORCE $(FILES) collection.bib
	python3 gen.py tweetverif.tex


depend:
		@echo $(FILES)

.PHONY: clean FORCE

clean:
	@echo cleaning...
	@rm -fr latex.out 2> /dev/null || true
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

spell:
	for f in $(TEX) ; do \
		aspell -t -c $$f; \
	done

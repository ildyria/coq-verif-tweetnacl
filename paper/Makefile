TEX := $(filter-out tweetverif.tex,$(wildcard *.tex))
FILES := $(TEX) $(wildcard tikz/*.tex) $(wildcard *.sty)

NO_COLOR="\033[0m"
RED = "\033[31m"
BRIGHTRED = "\033[91m"
YELLOW = "\033[93m"
ORANGE = "\033[33m"
GRAY = "\033[37m"
GREEN = "\033[32m"
BOLD = "\033[1m"


tweetverif.pdf: FORCE tweetverif.tex
	@echo $(BOLD)$(GREEN)"Building tweetverif.pdf"$(NO_COLOR)
	python3 latexrun.py tweetverif.tex

tweetverif.tex: FORCE $(FILES) collection.bib
	@echo $(BOLD)$(YELLOW)"Generating tweetverif.tex"$(NO_COLOR)
	python3 gen.py tweetverif.tex


depend:
		@echo $(FILES)

.PHONY: clean FORCE

clean:
	@echo $(BOLD)$(RED)"cleaning..."$(NO_COLOR)
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
	@rm *.bck 2> /dev/null || true
	@rm */*.aux 2> /dev/null || true
	@rm tweetverif.tex 2> /dev/null || true

spell:
	for f in $(TEX) ; do \
		aspell -t -c $$f; \
	done

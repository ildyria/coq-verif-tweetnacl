TEX := $(filter-out tweetverif.tex,$(wildcard *.tex))
FILES := $(TEX) $(wildcard tikz/*.tex) $(wildcard *.sty)

NO_COLOR="\033[0m"
RED = "\033[38;5;009m"
GREEN = "\033[38;5;010m"
YELLOW = "\033[38;5;011m"
ORANGE = "\033[38;5;214m"
LIGHTPURPLE = "\033[38;5;177m"
PURPLE = "\033[38;5;135m"
CYAN = "\033[38;5;014m"
LIGHTGRAY = "\033[38;5;252m"
DARKGRAY = "\033[38;5;242m"
BRIGHTRED = "\033[91m"
BOLD = "\033[1m"


tweetverif.pdf: FORCE tweetverif.tex
	@echo $(BOLD)$(GREEN)"Building tweetverif.pdf"$(NO_COLOR)$(DARKGRAY)
	python3 latexrun.py tweetverif.tex

tweetverif.tex: FORCE $(FILES) collection.bib
	@echo $(BOLD)$(YELLOW)"Generating tweetverif.tex"$(NO_COLOR)$(DARKGRAY)
	python3 gen.py tweetverif.tex
	@echo $(BOLD)$(GREEN)"Done."$(NO_COLOR)

specs_map.pdf: FORCE _files.tex
	@echo $(BOLD)$(GREEN)"Building specs_map.pdf"$(NO_COLOR)$(DARKGRAY)
	python3 latexrun.py _files.tex
	@echo $(BOLD)$(ORANGE)"Moving specs_map.pdf to ../"$(NO_COLOR)$(DARKGRAY)
	@mv _files.pdf ../specs_map.pdf


depend:
	@for f in $(FILES) ; do \
		echo $$f; \
	done

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
	@rm *.bak 2> /dev/null || true
	@rm */*.aux 2> /dev/null || true
	@rm tweetverif.tex 2> /dev/null || true

spell:
	@for f in $(TEX) ; do \
		aspell -t -c $$f; \
	done

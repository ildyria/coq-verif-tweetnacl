TEX := $(filter-out tweetverif.tex,$(wildcard *.tex))
FILES := $(TEX) $(wildcard tikz/*.tex) $(wildcard *.sty)
REVIEWS := _reviews.tex $(wildcard _reviews/*.tex) $(wildcard *.sty)

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


all: tweetverif.pdf reviews.pdf


# main pdf
tweetverif.pdf: FORCE tweetverif.tex tweetnacl.diff
	@echo $(BOLD)$(LIGHTPURPLE)"Building tweetverif.pdf"$(NO_COLOR)$(DARKGRAY)
	python3 latexrun.py tweetverif.tex

# main tex
tweetverif.tex: FORCE $(FILES) collection.bib
	@echo $(BOLD)$(YELLOW)"Generating tweetverif.tex"$(NO_COLOR)$(DARKGRAY)
	python3 gen.py tweetverif.tex

# list dependencies
depend:
	@for f in $(FILES) ; do \
		echo $$f; \
	done

.PHONY: clean FORCE

# generate diff between verified code and reference code
tweetnacl.diff:
	@echo $(BOLD)$(YELLOW)"Generating tweetnacl.diff"$(NO_COLOR)$(DARKGRAY)
	diff -u ../proofs/vst/c/tweetnacl.c ../proofs/vst/c/tweetnaclVerifiableC.c > tweetnacl.diff.tmp; [ $$? -eq 1 ]
	sed -i -e 1,2d tweetnacl.diff.tmp
	echo '--- tweetnacl.c' >> tweetnacl.diff
	echo '+++ tweetnaclVerifiableC.c' >> tweetnacl.diff
	cat tweetnacl.diff.tmp >> tweetnacl.diff
	rm tweetnacl.diff.tmp




clean:
	@echo $(BOLD)$(RED)"cleaning..."$(NO_COLOR)
	@rm -fr latex.out 2> /dev/null || true
	@rm tweetverif.pdf 2> /dev/null || true
	@rm reviews.pdf 2> /dev/null || true
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
	@rm tweetnacl.diff 2> /dev/null || true

# CHECK SPELLING
spell:
	@for f in $(TEX) ; do \
		aspell -t -c $$f; \
	done


# Bunch of other pdfs
feedback.pdf:
	@echo $(BOLD)$(LIGHTPURPLE)"Building feedback.pdf"$(NO_COLOR)$(DARKGRAY)
	python3 latexrun.py _includes/_feedback.tex
	@mv _feedback.pdf feedback.pdf

reviews.pdf: FORCE _reviews.tex $(REVIEWS)
	@echo $(BOLD)$(LIGHTPURPLE)"Building reviews.pdf"$(NO_COLOR)$(DARKGRAY)
	python3 latexrun.py _reviews.tex
	@mv _reviews.pdf reviews.pdf
	
# SPEC MAPS
specs_map.pdf: FORCE _files.tex
	@echo $(BOLD)$(LIGHTPURPLE)"Building specs_map.pdf"$(NO_COLOR)$(DARKGRAY)
	python3 latexrun.py _files.tex
	@echo $(BOLD)$(ORANGE)"Moving specs_map.pdf to ../"$(NO_COLOR)$(DARKGRAY)
	@mv _files.pdf ../specs_map.pdf



LATEXMK = ./latexrun.py
READ = evince
SOURCES := BenoitTweetNaCl.tex
DEPS := $(wildcard *.sty) ECC101/frame.tex
PDFS := $(notdir $(SOURCES:.tex=.pdf))

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

all: $(PDFS)

cleanpdf:
	@rm *.pdf 2> /dev/null || true

force: cleanpdf $(PDFS)

%.pdf: %.tex $(DEPS)
	@clear
	@echo $(BOLD)$(LIGHTPURPLE)"Building "$*".pdf"$(NO_COLOR)$(DARKGRAY)
	$(LATEXMK) $*.tex

open:
	${READ} $(PDFS)

clean:
	@echo $(BOLD)$(RED)"cleaning..."$(NO_COLOR)
	@rm -fr latex.out 2> /dev/null || true

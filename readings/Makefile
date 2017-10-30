FILES=$(wildcard *.md )
TEX=$(FILES:%.md=%.tex)
PDF=$(FILES:%.md=%.pdf)

all: $(TEX) $(PDF)

%.tex: %.md
	pandoc --from=markdown --output=$*.tex $*.md --to=latex --standalone

%.pdf: %.tex
	xelatex $*.tex

clean:
	@echo cleaning...
	@rm *.pdf 2> /dev/null || true
	@rm *.tex 2> /dev/null || true
	@rm *.toc 2> /dev/null || true
	@rm *.log 2> /dev/null || true
	@rm *.aux 2> /dev/null || true
	@rm *.out 2> /dev/null || true

DIST=coq-verif-tweetnacl

# NO_COLOR="\033[0m"
# RED = "\033[38;5;009m"
# GREEN = "\033[38;5;010m"
# YELLOW = "\033[38;5;011m"
# ORANGE = "\033[38;5;214m"
# LIGHTPURPLE = "\033[38;5;177m"
# PURPLE = "\033[38;5;135m"
# CYAN = "\033[38;5;014m"
# LIGHTGRAY = "\033[38;5;252m"
# DARKGRAY = "\033[38;5;242m"
# BRIGHTRED = "\033[91m"
# BOLD = "\033[1m"
#
# all: coq-tweetnacl-spec coq-tweetnacl-vst

include coq.mk

.PHONY: clean
clean: clean-spec clean-vst clean-dist

# build paper
.PHONY: paper
paper:
	@cd paper && $(MAKE)

clean-paper:
	cd paper && $(MAKE) clean

# generate artefact
$(DIST):
	@echo $(BOLD)$(ORANGE)"Creating $(DIST)"$(NO_COLOR)$(DARKGRAY)
	mkdir $(DIST)

$(DIST)/specs_map.pdf:
	@echo $(BOLD)$(YELLOW)"Building map for specs"$(NO_COLOR)$(DARKGRAY)
	cd paper && $(MAKE) specs_map.pdf
	mv specs_map.pdf $(DIST)/specs_map.pdf

dist: clean-dist $(DIST) $(DIST)/specs_map.pdf
	@echo $(BOLD)$(YELLOW)"Preparing $(DIST)"$(NO_COLOR)$(DARKGRAY)
	cp -r proofs $(DIST)
	mkdir $(DIST)/packages
	cp -r packages/coq-compcert $(DIST)/packages/
	cp -r packages/coq-reciprocity $(DIST)/packages/
	cp -r packages/coq-ssr-elliptic-curves $(DIST)/packages/
	cp -r packages/coq-vst $(DIST)/packages/
	cp repo $(DIST)/
	cp version $(DIST)/
	cp README.md $(DIST)/
	cp coq.mk $(DIST)/Makefile
	cp opam $(DIST)/
	@echo $(BOLD)$(LIGHTPURPLE)"Building $(DIST).tar.gz"$(NO_COLOR)$(DARKGRAY)
	tar -czvf $(DIST).tar.gz $(DIST)
	@echo $(BOLD)$(GREEN)"Done."$(NO_COLOR)

clean-dist:
	@echo $(BOLD)$(YELLOW)"removing $(DIST)"$(NO_COLOR)$(DARKGRAY)
	-rm -r $(DIST)
	-rm $(DIST).tar.gz
	@echo $(BOLD)$(GREEN)"Done."$(NO_COLOR)

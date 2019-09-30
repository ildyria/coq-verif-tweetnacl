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

all: deps coq-tweetnacl-spec coq-tweetnacl-vst


deps:
	@command -v opam >/dev/null 2>&1 || { \
		echo >&2 $(RED)"Error: opam is not installed.\n"$(NO_COLOR); \
		echo $(YELLOW)"Please do 'make readme' \n"$(NO_COLOR); exit 1; }

readme:
	less README.md


# DEFINE GENERIC ROUTINES (hidden via . prefix)
.configure1 .configure2:
	@echo $(BOLD)$(ORANGE)"Configuring $P"$(NO_COLOR)$(DARKGRAY)
	cd $P && $(SHELL) configure.sh

.building1: .configure1
.building2: .configure2 .building1
.building1 .building2:
	@echo $(BOLD)$(YELLOW)"Building $P"$(NO_COLOR)$(DARKGRAY)
	cd $P && $(MAKE) all
	@echo $(BOLD)$(LIGHTPURPLE)"Installing $P"$(NO_COLOR)$(DARKGRAY)
	cd $P && $(MAKE) install
	@echo $(BOLD)$(GREEN)"Done."$(NO_COLOR)

.dusting1: .configure1
.dusting2: .configure2
.dusting1 .dusting2:
	@echo $(BOLD)$(YELLOW)"Cleaning $P"$(NO_COLOR)$(DARKGRAY)
	cd $P && $(MAKE) clean
	cd $P && rm _CoqProject
	cd $P && rm Makefile
	cd $P && rm Makefile.conf

# DEFINE REAL TARGETS
coq-tweetnacl-spec: P=proofs/spec
coq-tweetnacl-spec: .building1

clean-spec: P=proofs/spec
clean-spec: .dusting1

coq-tweetnacl-vst: P=proofs/vst
coq-tweetnacl-vst: coq-tweetnacl-spec .building2

clean-vst: P=proofs/vst
clean-vst: .dusting2

.PHONY: clean
clean: clean-spec clean-vst

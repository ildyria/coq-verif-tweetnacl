all:
	$(MAKE) -C src all
	$(MAKE) -C toplevel all

test:
	$(MAKE) -C test all

clean:
	$(MAKE) -C src clean
	$(MAKE) -C toplevel clean
	$(MAKE) -C test clean

install:
	$(MAKE) -C src install
	$(MAKE) -C toplevel install

OCAMLFIND_DIR:=$(dir $(shell command -v ocamlfind 2>/dev/null))
OCAMLC_DIR:=$(dir $(shell command -v ocamlc 2>/dev/null))
NUM_INSTALLED:=$(shell ocamlfind query num 2>/dev/null)

ifeq ($(NUM_INSTALLED),)
# The num findlib package is not already present - wohoo!
OUR_FAULT=no
else
ifeq ($(OCAMLFIND_DIR),$(OCAMLC_DIR))
# The num findlib package is present, but ocamlc and ocamlfind are in the
# same place, which means that either we're looking at a system-installed
# ocamlfind (which isn't supported), or the user has done something else
# nefarious and doesn't deserve our sympathy (or, at least, our potentially
# unhelpful advice)
OUR_FAULT=no
else
# The num findlib package package is present, and ocamlc and ocamlfind reside
# in different directories, which means that we're almost certainly looking at
# a system switch which has been damaged by a previous num package installation
# on an OS which didn't protect the system lib directory.
OUR_FAULT=probably
endif
endif

findlib-install:
ifeq ($(OUR_FAULT),no)
	$(MAKE) -C src findlib-install
	$(MAKE) -C toplevel install
else
	@echo "\033[0;31m[ERROR]\033[m It appears that the num library was previously installed to your system"
	@echo "        compiler's lib directory, probably by a faulty opam package."
	@echo "        You will need to remove arith_flags.*, arith_status.*, big_int.*,"
	@echo "        int_misc.*, nat.*, num.*, ratio.*, nums.*, libnums.* and"
	@echo "        stublibs/dllnums.* from $(shell ocamlc -where)."
	@false
endif

uninstall:
	$(MAKE) -C src uninstall
	$(MAKE) -C toplevel uninstall

findlib-uninstall:
	$(MAKE) -C src findlib-uninstall
	$(MAKE) -C toplevel uninstall

.PHONY: all test clean install uninstall findlib-install findlib-uninstall

DIST=coq-verif-tweetnacl

all: coq-tweetnacl-spec coq-tweetnacl-vst

readme:
	less README.md


# DEFINE GENERIC ROUTINES (hidden via . prefix)
.configure1 .configure2:
	cd $P && $(SHELL) configure.sh

.building1: .configure1
.building2: .configure2
.building1 .building2:
	cd $P && $(MAKE) -j all
	cd $P && $(MAKE) install

.dusting1: .configure1
.dusting2: .configure2
.dusting1 .dusting2:
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
clean: clean-spec clean-vst clean-dist

# build paper
.PHONY: paper
paper:
	cd paper && $(MAKE)

clean-paper:
	cd paper && $(MAKE) clean

# generate artefact
$(DIST):
	mkdir $(DIST)

dist: $(DIST)
	cp -r proofs $(DIST)
	mkdir $(DIST)/packages
	cp -r packages/coq-compcert $(DIST)/packages/
	cp -r packages/coq-reciprocity $(DIST)/packages/
	cp -r packages/coq-ssr-elliptic-curves $(DIST)/packages/
	cp -r packages/coq-vst $(DIST)/packages/
	cp repo $(DIST)/
	cp version $(DIST)/
	cp README.md $(DIST)/
	cp Makefile $(DIST)/
	cp opam $(DIST)/
	tar -czvf $(DIST).tar.gz $(DIST)

clean-dist: $(DIST)
	rm -r $(DIST)
	-rm $(DIST).tar.gz

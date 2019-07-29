all: coq-tweetnacl-spec coq-tweetnacl-vst


coq-tweetnacl-spec:
	cd proofs/spec ;\
	./configure.sh ;\
	$(MAKE) -j ;\
	$(MAKE) install

coq-tweetnacl-vst: coq-tweetnacl-spec
	cd proofs/vst ;\
	./configure.sh ;\
	$(MAKE) -j ;\
	$(MAKE) install

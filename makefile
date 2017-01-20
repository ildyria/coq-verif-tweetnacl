default_target: .loadpath Libs ListsOp Op Car

#Note3: for SSReflect, one solution is to install MathComp 1.6
# somewhere add this line to a CONFIGURE file
# MATHCOMP=/my/path/to/mathcomp

DIRS= Libs ListsOp Op Car
INCLUDE= $(foreach a,$(DIRS),$(if $(wildcard $(a)), -Q $(a) $(a)))


PRELUDE = ../Prelude

# for Prelude
ifdef PRELUDE
 EXTFLAGS:=$(EXTFLAGS) -Q $(PRELUDE) Prelude
endif

# for SSReflect
ifdef MATHCOMP
 EXTFLAGS:=$(EXTFLAGS) -R $(MATHCOMP) mathcomp
endif

COQFLAGS=$(foreach d, $(DIRS), $(if $(wildcard $(d)), -Q $(d) $(d))) $(EXTFLAGS)
LIBPREFIX=Tweetnacl

ifdef LIBPREFIX
 COQFLAGS=$(foreach d, $(DIRS), $(if $(wildcard $(d)), -Q $(d) $(LIBPREFIX).$(d))) $(EXTFLAGS)
endif
DEPFLAGS:=$(COQFLAGS)

COQC=$(COQBIN)coqc
COQTOP=$(COQBIN)coqtop
COQDEP=$(COQBIN)coqdep $(DEPFLAGS)
COQDOC=$(COQBIN)coqdoc

COQVERSION= 8.5pl1 or-else 8.5pl2 or-else 8.5pl3 or-else 8.6beta1 or-else 8.6
COQV=$(shell $(COQC) -v)
ifeq ("$(filter $(COQVERSION),$(COQV))","")
	$(error FAILURE: You need Coq $(COQVERSION) but you have this version: $(COQV))
endif

define clean_files
	$($(1):%.v=$(2)/%.vo) \
	$($(1):%.v=$(2)/.%.aux) \
	$($(1):%.v=$(2)/.%.vo.aux) \
	$($(1):%.v=$(2)/%.glob) \
	$($(1):%.v=$(2)/%.v.crashcoqide)
endef




LIBS_FILES = $(notdir $(wildcard Libs/*.v))
LISTSOP_FILES = $(notdir $(wildcard ListsOp/*.v))
OP_FILES = $(notdir $(wildcard Op/*.v))
CAR_FILES = $(notdir $(wildcard Car/*.v))

FILES = \
 $(LIBS_FILES:%=Libs/%) \
 $(LISTSOP_FILES:%=ListsOp/%) \
 $(OP_FILES:%=Op/%) \
 $(CAR_FILES:%=Car/%)

CLEANFILES = $(call clean_files,LIBS_FILES,Libs) \
	$(call clean_files,LISTSOP_FILES,ListsOp) \
	$(call clean_files,OP_FILES,Op) \
	$(call clean_files,CAR_FILES,Car)

%_stripped.v: %.v
# e.g., 'make progs/verif_reverse_stripped.v will remove the tutorial comments
# from progs/verif_reverse.v
	grep -v '^.[*][*][ )]' $*.v >$@

%.vo: %.v
	@echo COQC $*.v
ifeq ($(TIMINGS), true)
#	bash -c "wc $*.v >>timings; date +'%s.%N before' >> timings; $(COQC) $(COQFLAGS) $*.v; date +'%s.%N after' >>timings" 2>>timings
	@bash -c "/bin/time --output=TIMINGS -a -f '%e real, %U user, %S sys, '\"$(shell wc $*.v)\" $(COQC) $(COQFLAGS) $*.v"
#	echo -n $*.v " " >>TIMINGS; bash -c "/usr/bin/time -o TIMINGS -a $(COQC) $(COQFLAGS) $*.v"
else
	@$(COQC) $(COQFLAGS) $*.v
endif

all: .loadpath $(FILES:.v=.vo)

Libs: 		.loadpath $(LIBS_FILES:%.v=Libs/%.vo)
ListsOp:	.loadpath $(LISTSOP_FILES:%.v=ListsOp/%.vo)
Op:			.loadpath $(OP_FILES:%.v=Op/%.vo)
Car:		.loadpath $(CAR_FILES:%.v=Car/%.vo)

.loadpath:
	echo $(COQFLAGS) > .loadpath

dep:
	@$(COQDEP) $(filter $(wildcard *.v */*.v */*/*.v),$(FILES))
	# $(COQDEP) > .depend $(FILES)
	# $(COQDEP) >.depend `find Libs/ -name "*.v"`
	# $(COQDEP) >.depend `find . -name "*.v"`

.depend:
	$(COQDEP) $(filter $(wildcard *.v */*.v */*/*.v),$(FILES))  > .depend

depend:
	$(COQDEP) $(filter $(wildcard *.v */*.v */*/*.v),$(FILES))  > .depend

clean:
	rm -f $(CLEANFILES) .loadpath .depend .nia.cache .lia.cache

count:
	wc $(FILES)

# The .depend file is divided into two parts, .depend and .depend-concur,
# in order to work around a limitation in Cygwin about how long one
# command line can be.  (Or at least, it seems to be a solution to some
# such problem, not sure exactly.  -- Andrew)
-include .depend
-include .depend-concur
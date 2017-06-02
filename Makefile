default_target: .loadpath Libs ListsOp Op Car Montgomery

#Note3: for SSReflect, one solution is to install MathComp 1.6
# somewhere add this line to a CONFIGURE file
# MATHCOMP=/my/path/to/mathcomp


VERBOSE?=
SHOW := $(if $(VERBOSE),@true "",@echo "")
HIDE := $(if $(VERBOSE),,@)


DIRS= Libs ListsOp Op Car Montgomery
INCLUDE= $(foreach a,$(DIRS),$(if $(wildcard $(a)), -Q $(a) $(a)))


COQSTDPP = ../coq-stdpp/theories
COQPRIME = Coqprime

# for Coq-stdpp
ifdef COQSTDPP
 EXTFLAGS:=$(EXTFLAGS) -R $(COQSTDPP) stdpp
endif


# for Coq-stdpp
ifdef COQPRIME
 EXTFLAGS:=$(EXTFLAGS) -R $(COQPRIME)/Tactic Coqprime
 EXTFLAGS:=$(EXTFLAGS) -R $(COQPRIME)/N Coqprime
 EXTFLAGS:=$(EXTFLAGS) -R $(COQPRIME)/Z Coqprime
 EXTFLAGS:=$(EXTFLAGS) -R $(COQPRIME)/List Coqprime
 EXTFLAGS:=$(EXTFLAGS) -R $(COQPRIME)/PrimalityTest Coqprime
 EXTFLAGS:=$(EXTFLAGS) -R $(COQPRIME)/elliptic Coqprime
 EXTFLAGS:=$(EXTFLAGS) -R $(COQPRIME)/num Coqprime
 EXTFLAGS:=$(EXTFLAGS) -R $(COQPRIME)/examples Coqprime
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
COQDOC=$(COQBIN)coqdoc -d doc -g -utf8 $(DEPFLAGS)

COQVERSION= 8.6
COQV=$(shell $(COQC) -v)
ifeq ("$(filter $(COQVERSION),$(COQV))","")
	$(error FAILURE: You need Coq $(COQVERSION) but you have this version: $(COQV))
endif

define clean_files
	$($(1):%.v=$(2)/%.v.d) \
	$($(1):%.v=$(2)/%.vio) \
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
MONTGOMERY_FILES = $(notdir $(wildcard Montgomery/*.v))

FILES = \
 $(MONTGOMERY_FILES:%=Montgomery/%) \
 $(LIBS_FILES:%=Libs/%) \
 $(LISTSOP_FILES:%=ListsOp/%) \
 $(OP_FILES:%=Op/%) \
 $(CAR_FILES:%=Car/%) \

ifneq ($(filter-out archclean clean cleanall printenv,$(MAKECMDGOALS)),)
-include $(addsuffix .d,$(FILES))
else
ifeq ($(MAKECMDGOALS),)
-include $(addsuffix .d,$(FILES))
endif
endif

CLEANFILES = $(call clean_files,LIBS_FILES,Libs) \
	$(call clean_files,LISTSOP_FILES,ListsOp) \
	$(call clean_files,OP_FILES,Op) \
	$(call clean_files,CAR_FILES,Car) \
	$(call clean_files,MONTGOMERY_FILES,Montgomery)

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

%.vio: %.v
	@echo COQC $*.v
ifeq ($(TIMINGS), true)
#	bash -c "wc $*.v >>timings; date +'%s.%N before' >> timings; $(COQC) $(COQFLAGS) $*.v; date +'%s.%N after' >>timings" 2>>timings
	@bash -c "/bin/time --output=TIMINGS -a -f '%e real, %U user, %S sys, '\"$(shell wc $*.v)\" $(COQC) $(COQFLAGS) $*.v"
#	echo -n $*.v " " >>TIMINGS; bash -c "/usr/bin/time -o TIMINGS -a $(COQC) $(COQFLAGS) $*.v"
else
	@$(COQC) -quick $(COQFLAGS) $*.v
endif

all: .loadpath $(FILES:.v=.vo)
quick: .loadpath $(FILES:.v=.vio)

Libs: 		.loadpath $(LIBS_FILES:%.v=Libs/%.vo)
ListsOp:	.loadpath $(LISTSOP_FILES:%.v=ListsOp/%.vo)
Op:		.loadpath $(OP_FILES:%.v=Op/%.vo)
Car:		.loadpath $(CAR_FILES:%.v=Car/%.vo)
Montgomery:	.loadpath $(MONTGOMERY_FILES:%.v=Montgomery/%.vo)

_CoqProject: Makefile
	$(SHOW)Generate _CoqProject
	$(HIDE)echo $(COQFLAGS) >_CoqProject

.loadpath: Makefile _CoqProject
	$(SHOW)Generate .loadpath
	$(HIDE)echo $(COQFLAGS) > .loadpath


doc:
	mkdir -p doc
	$(COQDOC) $(FILES)

$(addsuffix .d,$(FILES)): %.v.d: %.v
	$(SHOW)'COQDEP $<'
	$(HIDE)$(COQDEP) $(COQLIBS) "$<" > "$@" || ( RV=$$?; rm -f "$@"; exit $${RV} )

clean:
	$(SHOW)cleaning files...
	$(HIDE)rm -f $(CLEANFILES) .loadpath _CoqProject .depend .nia.cache .lia.cache

# check: quick
# 	coqtop -schedule-vio2vo

vio2vo: quick
	$(COQC) $(COQFLAGS) -schedule-vio2vo $(J) $(FILES:%.v=%.vio)

checkproofs:
	$(COQC) $(COQDEBUG) $(COQFLAGS) -schedule-vio-checking $(J) $(FILES:%.v=%.vio)

count:
	wc $(FILES)

printenv:
	@"$(COQTOP)" -config
	@echo 'CAMLC =	$(CAMLC)'
	@echo 'CAMLOPTC =	$(CAMLOPTC)'
	@echo 'PP =	$(PP)'
	@echo 'COQFLAGS =	$(COQFLAGS)'
	@echo 'COQLIBINSTALL =	$(COQLIBINSTALL)'
	@echo 'COQDOCINSTALL =	$(COQDOCINSTALL)'

# The .depend file is divided into two parts, .depend and .depend-concur,
# in order to work around a limitation in Cygwin about how long one
# command line can be.  (Or at least, it seems to be a solution to some
# such problem, not sure exactly.  -- Andrew)
-include .depend
-include .depend-concur

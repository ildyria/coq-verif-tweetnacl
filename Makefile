default_target: .loadpath Libs ListsOp Mid Low Car Sel Unpack

all: default_target High

#Note3: for SSReflect, one solution is to install MathComp 1.6
# somewhere add this line to a CONFIGURE file
# MATHCOMP=/my/path/to/mathcomp


VERBOSE?=
SHOW := $(if $(VERBOSE),@true "",@echo "")
HIDE := $(if $(VERBOSE),,@)


DIRS= Libs ListsOp Mid Car Sel High Unpack
INCLUDE= $(foreach a,$(DIRS),$(if $(wildcard $(a)), -Q $(a) $(a)))

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

COQVERSION= 8.7.0
COQV=$(shell $(COQC) -v)
ifeq ("$(filter $(COQVERSION),$(COQV))","")
	$(error FAILURE: You need Coq $(COQVERSION) but you have this version: $(COQV))
endif

LIBS_FILES = $(wildcard Libs/*.v)
LISTSOP_FILES = $(wildcard ListsOp/*.v)
MID_FILES = $(wildcard Mid/*.v)
CAR_FILES = $(wildcard Car/*.v)
SEL_FILES = $(wildcard Sel/*.v)
UNPACK_FILES = $(wildcard Unpack/*.v)
HIGH_FILES = $(wildcard High/*.v)

COUNTFILES = $(LIBS_FILES) $(LISTSOP_FILES) $(MID_FILES) $(CAR_FILES) \
 $(SEL_FILES) $(UNPACK_FILES)


FILES = $(COUNTFILES) $(HIGH_FILES)

ifneq ($(filter-out archclean clean cleanall printenv count,$(MAKECMDGOALS)),)
-include $(addsuffix .d,$(FILES))
else
ifeq ($(MAKECMDGOALS),)
-include $(addsuffix .d,$(FILES))
endif
endif

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

Libs: 		.loadpath $(LIBS_FILES:%.v=%.vo)
ListsOp:	.loadpath $(LISTSOP_FILES:%.v=%.vo)
Mid:		.loadpath $(MID_FILES:%.v=%.vo)
Car:		.loadpath $(CAR_FILES:%.v=%.vo)
Sel:		.loadpath $(SEL_FILES:%.v=%.vo)
Unpack:		.loadpath $(UNPACK_FILES:%.v=%.vo)
High:		.loadpath $(HIGH_FILES:%.v=%.vo)

_CoqProject: Makefile
	$(SHOW)Generate _CoqProject
	$(HIDE)echo $(COQFLAGS) >_CoqProject

.loadpath: _CoqProject
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
	$(HIDE)rm -f $(wildcard */*.d) $(wildcard */*.vo) $(wildcard */*.glob) $(wildcard */.*.aux) .loadpath _CoqProject .depend .nia.cache .lia.cache

# check: quick
# 	coqtop -schedule-vio2vo

vio2vo: quick
	$(COQC) $(COQFLAGS) -schedule-vio2vo $(J) $(FILES:%.v=%.vio)

checkproofs:
	$(COQC) $(COQDEBUG) $(COQFLAGS) -schedule-vio-checking $(J) $(FILES:%.v=%.vio)

count:
	wc -l $(COUNTFILES)

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

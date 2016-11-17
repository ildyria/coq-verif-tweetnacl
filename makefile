COQ = coqc

all:
	@echo genereting Tactical libs
	${COQ} LibTactics.v
	${COQ} Libs.v
	@echo generating tools and libs
	${COQ} Tools.v
	${COQ} notations.v
	${COQ} Forall.v
	${COQ} Forall_extended.v
	${COQ} ZofList.v
	${COQ} Reduce.v
	${COQ} Carry.v
	${COQ} SumList.v
	${COQ} ScalarMult.v
	@echo generating libs for iterator
	${COQ} A.v
	${COQ} M.v

clean:
	@echo cleaning...
	@rm *.vo 2> /dev/null || true
	@rm *.glob 2> /dev/null || true
	@rm *.vio 2> /dev/null || true
	@rm .*.aux 2> /dev/null || true

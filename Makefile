.PHONY: coq clean corn


COQPATH?="${CURDIR}/dependencies"
export COQPATH

coq: Makefile.coq
	COQPATH="$(COQPATH)" $(MAKE) -f Makefile.coq

Makefile.coq: Makefile _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

corn: dependencies/CoRN
	$(MAKE) -C dependencies/CoRN

clean:: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq

print-coqpath::
	@echo "COQPATH=$$COQPATH"

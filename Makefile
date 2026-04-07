LIBNAME=Multivariate

.SUFFIXES:

.PHONY: default
default: rocq.mk
	$(MAKE) -f rocq.mk

rocq.mk: _CoqProject
	rocq makefile -f _CoqProject -o $@

_CoqProject:
	echo "-R . $(LIBNAME) ." > $@

.PHONY: clean
clean: rocq.mk
	$(MAKE) -f rocq.mk $@
	rm -f _CoqProject rocq.mk rocq.mk.conf

%:
	$(MAKE) -f rocq.mk $@

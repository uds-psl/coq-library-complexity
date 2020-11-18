all: Makefile.coq deps
	$(MAKE) -f Makefile.coq all

deps:
	$(MAKE) -C coq-library-undecidability all

html: Makefile.coq
	$(MAKE) -f Makefile.coq html
	mv html/*.html ./website
	rm -rf html

install: Makefile.coq
	$(MAKE) -f Makefile.coq install

uninstall: Makefile.coq
	$(MAKE) -f Makefile.coq uninstall

clean: Makefile.coq
	$(MAKE) -C coq-library-undecidability clean
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq Makefile.coq.conf

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

.PHONY: all install html clean

dummy:

%.vo: Makefile.coq dummy
	$(MAKE) -f Makefile.coq $@

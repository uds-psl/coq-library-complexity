all: Makefile.coq
	$(MAKE) -f Makefile.coq all

html: Makefile.coq
	$(MAKE) -f Makefile.coq html
	mv html/*.html ./website
	rm -rf html

install: Makefile.coq
	$(MAKE) -f Makefile.coq install

uninstall: Makefile.coq
	$(MAKE) -f Makefile.coq uninstall

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq Makefile.coq.conf $(TMP_COQPROJECT)

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

.PHONY: all install html clean

dummy:

force _CoqProject Makefile: ;

%: Makefile.coq force
	@+$(MAKE) -f Makefile.coq $@

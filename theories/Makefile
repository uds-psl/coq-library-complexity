all: Makefile.coq
	+make -f Makefile.coq L/Complexity/Reductions/Cook/SingleTMGenNP_to_TCC.vo all

html: Makefile.coq
	+make -f Makefile.coq html
	mv html/*.html ../website
	rm -rf html

install: Makefile.coq
	+make -f Makefile.coq install

uninstall: Makefile.coq
	+make -f Makefile.coq uninstall

clean: Makefile.coq
	+make -f Makefile.coq clean
	rm -f Makefile.coq Makefile.coq.conf

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

.PHONY: all html clean

dummy:

%.vo: Makefile.coq dummy
	+make -f Makefile.coq $@

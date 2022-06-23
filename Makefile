all: Makefile.coq
	$(MAKE) -f Makefile.coq all

depsopam:
	opam repo add coq-released https://coq.inria.fr/opam/released
	opam pin add -n -y -k git coq-metacoq-template.dev+8.15 "https://github.com/MetaCoq/metacoq.git#9493bb6"
	opam pin add -y coq-library-undecidability https://github.com/fakusb/coq-library-undecidability.git#9a499d688e920bbe0485578e41ad9dde48e32551
	opam install . --deps-only

VFILES_LIB_UNDEC = $(shell grep -P '^(TM|(L(?!\/Reductions\/)))(\/[^\/\s]+)*\.v' coq-library-undecidability/theories/_CoqProject 2> /dev/null)

VOFILES_LIB_UNDEC := $(VFILES_LIB_UNDEC:=o)

depssubmodule:
	git submodule update  
	opam install ./coq-library-undecidability --deps-only
	$(MAKE) -C coq-library-undecidability/theories -f Makefile Makefile.coq
	$(MAKE) -C coq-library-undecidability/theories -f Makefile.coq only TGTS="$(VOFILES_LIB_UNDEC)"

depssubmodule_makeonly:
	$(MAKE) -C coq-library-undecidability/theories -f Makefile Makefile.coq
	$(MAKE) -C coq-library-undecidability/theories -f Makefile.coq only TGTS="$(VOFILES_LIB_UNDEC)"

html: Makefile.coq
	$(MAKE) -f Makefile.coq html
	mv html/*.html ./website
	rm -rf html

install: Makefile.coq
	$(MAKE) -f Makefile.coq install

uninstall: Makefile.coq
	$(MAKE) -f Makefile.coq uninstall

realclean: Makefile.coq clean
	$(MAKE) -C coq-library-undecidability/theories -f Makefile clean

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq Makefile.coq.conf $(TMP_COQPROJECT)

TMP_COQPROJECT := "._CoqProject.tmp"

Makefile.coq: _CoqProject
	./adjustCoqProject.sh $(TMP_COQPROJECT)
	coq_makefile -f $(TMP_COQPROJECT) -o Makefile.coq

.PHONY: all install html clean

dummy:

force _CoqProject Makefile: ;

%: Makefile.coq force
	@+$(MAKE) -f Makefile.coq $@

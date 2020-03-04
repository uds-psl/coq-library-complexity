TOPTARGETS := all clean

SUBDIRS := $(wildcard */.)
SUBDIRS := $(filter-out template-coq/., $(SUBDIRS))

template-coq/.:
	$(MAKE) -C "template-coq/template-coq/." all

$(TOPTARGETS): $(SUBDIRS)
$(SUBDIRS):
	$(MAKE) -C $@ $(MAKECMDGOALS)

.PHONY: $(TOPTARGETS) $(SUBDIRS) template-coq/.
all: $(SUBDIRS) template-coq/.

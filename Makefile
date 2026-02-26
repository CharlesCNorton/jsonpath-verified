COQPROJECT ?= _CoqProject
COQMAKEFILE ?= CoqMakefile
COQBIN ?= /home/zootest/.opam/certicoq-8.20/bin/
COQMAKEFILE_TOOL ?= $(COQBIN)coq_makefile

.PHONY: all clean distclean regen

all: $(COQMAKEFILE)
	$(MAKE) -f $(COQMAKEFILE) COQBIN="$(COQBIN)" all

$(COQMAKEFILE): $(COQPROJECT)
	$(COQMAKEFILE_TOOL) -f $(COQPROJECT) -o $(COQMAKEFILE)

regen:
	$(COQMAKEFILE_TOOL) -f $(COQPROJECT) -o $(COQMAKEFILE)

clean: $(COQMAKEFILE)
	$(MAKE) -f $(COQMAKEFILE) COQBIN="$(COQBIN)" clean

distclean:
	@if [ -f "$(COQMAKEFILE)" ]; then $(MAKE) -f $(COQMAKEFILE) COQBIN="$(COQBIN)" clean; fi
	@rm -f $(COQMAKEFILE) $(COQMAKEFILE).conf

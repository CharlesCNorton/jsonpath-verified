COQPROJECT ?= _CoqProject
COQMAKEFILE ?= CoqMakefile
COQBIN ?= /home/zootest/.opam/certicoq-8.20/bin/
COQMAKEFILE_TOOL ?= $(COQBIN)coq_makefile
ifeq ($(OS),Windows_NT)
PYTHON ?= py -3
else
PYTHON ?= python3
endif

.PHONY: all clean distclean regen proof-hygiene

all: $(COQMAKEFILE)
	$(MAKE) -f $(COQMAKEFILE) COQBIN="$(COQBIN)" all

$(COQMAKEFILE): $(COQPROJECT)
	$(COQMAKEFILE_TOOL) -f $(COQPROJECT) -o $(COQMAKEFILE)

regen:
	$(COQMAKEFILE_TOOL) -f $(COQPROJECT) -o $(COQMAKEFILE)

proof-hygiene:
	@$(PYTHON) scripts/proof_hygiene.py

clean: $(COQMAKEFILE)
	$(MAKE) -f $(COQMAKEFILE) COQBIN="$(COQBIN)" clean

distclean:
	@if [ -f "$(COQMAKEFILE)" ]; then $(MAKE) -f $(COQMAKEFILE) COQBIN="$(COQBIN)" clean; fi
	@rm -f $(COQMAKEFILE) $(COQMAKEFILE).conf

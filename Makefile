COQPROJECT ?= _CoqProject
COQMAKEFILE ?= CoqMakefile
COQBIN ?= /home/zootest/.opam/certicoq-8.20/bin/
COQMAKEFILE_TOOL ?= $(COQBIN)coq_makefile

.PHONY: all clean distclean regen proof-hygiene

all: $(COQMAKEFILE)
	$(MAKE) -f $(COQMAKEFILE) COQBIN="$(COQBIN)" all

$(COQMAKEFILE): $(COQPROJECT)
	$(COQMAKEFILE_TOOL) -f $(COQPROJECT) -o $(COQMAKEFILE)

regen:
	$(COQMAKEFILE_TOOL) -f $(COQPROJECT) -o $(COQMAKEFILE)

proof-hygiene:
	@if command -v rg >/dev/null 2>&1; then \
		FIND_CMD="rg -n '\\b(Admitted|Axiom)\\b' -g '*.v' ."; \
	else \
		FIND_CMD="grep -R -n -E '\\b(Admitted|Axiom)\\b' --include='*.v' ."; \
	fi; \
	if eval $$FIND_CMD >/dev/null 2>&1; then \
		echo "proof hygiene FAILED: found Admitted/Axiom."; \
		eval $$FIND_CMD; \
		exit 1; \
	else \
		echo "proof hygiene OK: no Admitted/Axiom in project .v files."; \
	fi

clean: $(COQMAKEFILE)
	$(MAKE) -f $(COQMAKEFILE) COQBIN="$(COQBIN)" clean

distclean:
	@if [ -f "$(COQMAKEFILE)" ]; then $(MAKE) -f $(COQMAKEFILE) COQBIN="$(COQBIN)" clean; fi
	@rm -f $(COQMAKEFILE) $(COQMAKEFILE).conf

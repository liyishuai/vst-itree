COQMAKEFILE?=Makefile.coq

all: $(COQMAKEFILE)
	$(MAKE) -f $^ $@

clean: $(COQMAKEFILE)
	$(MAKE) -f $^ $@
	$(RM) $(COQMAKEFILE) $(COQMAKEFILE).conf

$(COQMAKEFILE): _CoqProject
	$(COQBIN)coq_makefile -f $^ -o $@

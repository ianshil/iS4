COQMAKEFILE ?= Makefile.coq
EXTRA_DIR:= doc-config
COQDOCEXTRAFLAGS = -s
COQDOCJS_LN = true
COQ_PROJ ?= _CoqProject
COQDOCJS_DIR ?= coqdocjs
COQDOCFLAGS ?= \
  --toc --toc-depth 2 --html --interpolate \
	-d docs \
  --index indexpage --no-lib-name --parse-comments \
  --with-header $(EXTRA_DIR)/header.html --with-footer $(EXTRA_DIR)/footer.html
export COQDOCFLAGS
SUBDIR_ROOTS := theories
DIRS := . $(shell find $(SUBDIR_ROOTS) -type d)

all: $(COQMAKEFILE)
	$(MAKE) -f $^ $@

clean: $(COQMAKEFILE)
	$(MAKE) -f $^ cleanall
	$(RM) $^ $^.conf

$(COQMAKEFILE): $(COQ_PROJ)
	$(COQBIN)coq_makefile -f $^ -o $@

force $(COQ_PROJ) Makefile: ;

%: $(COQMAKEFILE) force
	@+$(MAKE) -f $< $@

doc: makefile.coq
	rm -fr html docs/*
	@$(MAKE) -f makefile.coq html
	cp html/* docs
	cp $(EXTRA_DIR)/resources/* docs

.PHONY: clean all force

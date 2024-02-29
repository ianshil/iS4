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
PUBLIC_URL="https://ianshil.github.io/iS4"
SUBDIR_ROOTS := theories
DIRS := . $(shell find $(SUBDIR_ROOTS) -type d)

_: makefile.coq

makefile.coq:
	coq_makefile -f _CoqProject -docroot docs -o $@

all: $(COQMAKEFILE)
	$(MAKE) -f $^ $@

clean: $(COQMAKEFILE)
	$(MAKE) -f $^ cleanall
	$(RM) $^ $^.conf

doc: makefile.coq
	rm -fr html docs/*
	@$(MAKE) -f makefile.coq html
	cp html/* docs
	cp $(EXTRA_DIR)/resources/* docs

.PHONY: clean all force

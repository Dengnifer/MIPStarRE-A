# Makefile for the paper-gap notes.
#
# Each note in this directory is a standalone LaTeX document that justifies one
# correction made to a source-paper statement during formalization.  They are
# the reviewer-facing half of the qpbt-gap-register.md summary table, so a
# reviewer must be able to build them with a stock TeX installation and nothing
# else.  This Makefile is that path: plain latexmk, no external tooling.
#
#   make          compile every note into build/ (also `make all`)
#   make check    compile, then fail on any LaTeX error, undefined reference,
#                 undefined citation or multiply-defined label
#   make pages    print the page count of every built note
#   make clean    remove build/
#
# The repository's own CI runs `texra-blueprint --root . paper-gaps check`
# (local/bin/ci.sh, step `paper-gaps`), which validates cross-note slugs and
# registered source keys.  That check and this Makefile are complementary: the
# CI step needs texra-blueprint, this one does not.
#
# build/ is ignored (see the repository .gitignore); no PDF is committed.  The
# artifact packaging step builds the PDFs at release time.

LATEXMK      ?= latexmk
BUILDDIR     := build
LATEXMKFLAGS := -pdf -interaction=nonstopmode -halt-on-error -file-line-error \
                -output-directory=$(BUILDDIR)

# Every .tex in this directory that is a document in its own right.  command.tex
# is a macro file included by the notes and must not be compiled on its own.
NOTES := $(shell grep -l '^[[:space:]]*\\documentclass' *.tex 2>/dev/null | LC_ALL=C sort)
PDFS  := $(NOTES:%.tex=$(BUILDDIR)/%.pdf)

.PHONY: all check clean list pages
.DELETE_ON_ERROR:

all: $(PDFS)

$(BUILDDIR):
	@mkdir -p $(BUILDDIR)

$(BUILDDIR)/%.pdf: %.tex command.tex references.bib | $(BUILDDIR)
	$(LATEXMK) $(LATEXMKFLAGS) $<

list:
	@for n in $(NOTES); do echo "$$n"; done

pages: all
	@for n in $(NOTES); do \
	  pdf=$(BUILDDIR)/$${n%.tex}.pdf; \
	  if command -v pdfinfo >/dev/null 2>&1; then \
	    p=$$(pdfinfo "$$pdf" 2>/dev/null | awk '/^Pages:/ {print $$2}'); \
	  else \
	    p=$$(grep -c '/Type[[:space:]]*/Page[^s]' "$$pdf" 2>/dev/null); \
	  fi; \
	  printf '%-60s %s\n' "$$n" "$${p:-?}"; \
	done

# A LaTeX error already fails `all`, because -halt-on-error makes latexmk exit
# non-zero.  What latexmk does NOT fail on is an unresolved \ref or \cite or a
# duplicated label, so scan the logs for those.  Anchoring on the warning
# prefix rather than on the word "undefined" keeps the match reliable: LaTeX
# wraps log lines at 79 columns, and it emits "LaTeX Warning: Reference ..." /
# "LaTeX Warning: Citation ..." only when the key is unresolved.
check: all
	@status=0; \
	for n in $(NOTES); do \
	  base=$${n%.tex}; log=$(BUILDDIR)/$$base.log; pdf=$(BUILDDIR)/$$base.pdf; \
	  if [ ! -s "$$pdf" ]; then \
	    echo "ERROR: $$n produced no PDF"; status=1; \
	  fi; \
	  if [ ! -f "$$log" ]; then \
	    echo "ERROR: $$n produced no log"; status=1; continue; \
	  fi; \
	  bad=$$(grep -E '^LaTeX Warning: (Reference|Citation) |undefined references|multiply defined|^! |^Emergency stop|^Fatal error' "$$log" || true); \
	  if [ -n "$$bad" ]; then \
	    echo "ERROR: $$n"; printf '%s\n' "$$bad" | sed 's/^/    /'; status=1; \
	  fi; \
	done; \
	if [ $$status -ne 0 ]; then \
	  echo "paper-gaps check: FAILED"; exit 1; \
	fi; \
	echo "paper-gaps check: $(words $(NOTES)) notes built, no LaTeX errors, no undefined references"

clean:
	rm -rf $(BUILDDIR)

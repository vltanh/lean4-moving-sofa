# Build the manuscript and the source archive for arXiv.
#
#   make            build main.pdf
#   make figures    redraw the figures in figures/ (python3 with numpy and matplotlib)
#   make arxiv      build arxiv/gerver-sofa-uniqueness.tar.gz, the files to upload to arXiv,
#                   and check that they compile on their own
#   make clean      remove the build products

MAIN := main
SRC  := $(MAIN).tex macros.tex refs.bib $(wildcard sections/*.tex) $(wildcard figures/*.pdf)
TAR  := arxiv/gerver-sofa-uniqueness.tar.gz

.PHONY: pdf figures arxiv clean
pdf: $(MAIN).pdf

$(MAIN).pdf: $(SRC)
	latexmk -pdf -interaction=nonstopmode -halt-on-error $(MAIN).tex

figures:
	python3 figures/make_figures.py

# arXiv compiles the upload itself, with its own BibTeX run only when there is no .bbl, so the
# archive carries the .bbl; the test build below uses pdflatex alone, like a fresh checkout.
arxiv: $(MAIN).pdf
	rm -rf arxiv
	mkdir -p arxiv/src/sections arxiv/src/figures
	cp $(MAIN).tex macros.tex $(MAIN).bbl arxiv/src/
	cp sections/*.tex arxiv/src/sections/
	cp figures/*.pdf arxiv/src/figures/
	cd arxiv/src && pdflatex -interaction=nonstopmode -halt-on-error $(MAIN).tex >/dev/null \
	  && pdflatex -interaction=nonstopmode -halt-on-error $(MAIN).tex >/dev/null \
	  && pdflatex -interaction=nonstopmode -halt-on-error $(MAIN).tex >/dev/null
	@if grep -q "undefined" arxiv/src/$(MAIN).log; then echo "undefined references in the test build"; exit 1; fi
	tar -czf $(TAR) -C arxiv/src $(MAIN).tex macros.tex $(MAIN).bbl sections figures
	@echo "$(TAR): $$(tar -tzf $(TAR) | wc -l) entries, test build $$(pdfinfo arxiv/src/$(MAIN).pdf | grep Pages)"

clean:
	latexmk -C $(MAIN).tex
	rm -rf arxiv

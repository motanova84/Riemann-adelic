LATEX=pdflatex
BIBTEX=bibtex
MAIN=main

all:
$(LATEX) $(MAIN).tex
$(BIBTEX) $(MAIN)
$(LATEX) $(MAIN).tex
$(LATEX) $(MAIN).tex

clean:
rm -f *.aux *.log *.out *.toc *.bbl *.blg *.pdf

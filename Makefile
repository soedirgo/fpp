COQDOC = coqdoc --latex --short --table-of-contents
PDFLATEX = pdflatex

FILES = week-01_functional-programming-in-Coq week-02_exercises week-03_specifications week-04_backward-and-forward-proofs

# Substitution References
VFILES = $(FILES:%=%.v)
PDFFILES = $(FILES:%=%.pdf)

.PRECIOUS: %.tex

all: $(PDFFILES)

%.tex: %.v
	$(COQDOC) $(VFILES)

%.pdf: %.tex
	$(PDFLATEX) $*
	$(PDFLATEX) $*

clean:
	rm *.aux *.log *.out *.pdf *.tex *.toc

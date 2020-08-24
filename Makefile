COQDOC = coqdoc --latex --short --table-of-contents
PDFLATEX = pdflatex

FILES =

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

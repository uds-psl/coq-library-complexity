.PHONY: all clean thesis thesis.pdf

all: thesis

thesis: thesis.pdf

thesis.pdf: thesis.tex
	    "latexmk" -pdf thesis.tex
clean:
	rm -rf *.out *.dvi *.log *.out *.aux *.pdf *.bbl *.blg *.fdb_latexmk *.glo *.glsdefs *.ist *.synctex *.thm *.toc *.tdo *.fls

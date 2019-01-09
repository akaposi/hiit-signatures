all: paper.pdf

%.pdf : %.tex
	latexmk -pdf $<

clean:
	rm -f *.aux *.bbl *.blg *.fdb_latexmk *.fls *.log *.out *.nav *.snm *.toc *.vtc *.ptb *~ paper.pdf

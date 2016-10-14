# Sourcefiles
MEXT=md
SRC=$(wildcard *.$(MEXT))
PDF=$(SRC:.md=.pdf)
TEX=$(SRC:.md=.tex)

# Latexmk/pandoc options
LATEXMKOPT=-pdf
LATEX=pdflatex
LATEXOPT=--shell-escape
OUT=latex

all:	$(PDF) $(TEX)

watch: $(SRC)
	@echo Watching for changes...
	@fswatch -o $^ | xargs -n1 -I{} make

%.tex: %.md
	@pandoc -t $(OUT) $(SRC) -o $(TEX) -s

%.pdf: %.tex
	@latexmk $(LATEXMKOPT) -pdflatex="$(LATEX) $(LATEXOPT) %O %S" $(TEX) --silent

clean:
	@latexmk -c $(TEX)
	rm -rf *~ *.tmp
	rm -f *.nav *.snm *.tex *.bcf *.bbl *.blg *.aux *.end *.fls *.log *.out *.fdb_latexmk *.xml *.gz *.vrb

.PHONY: all watch clean

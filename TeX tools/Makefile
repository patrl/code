# Sourcefiles
MEXT=md
SRCS=$(wildcard *.$(MEXT))
PDFS=$(SRCS:.md=.pdf)
TEXS=$(SRCS:.md=.tex)

# Latexmk/pandoc options
LATEXMKOPT=-pdf
LATEX=pdflatex
LATEXOPT=--shell-escape
OUT=latex
FLAG=

all:	$(PDFS) $(TEXS)

watch: $(SRCS)
	@echo Watching for changes...
	@fswatch -o $^ | xargs -n1 -I{} make

%.tex: %.md
	@pandoc -t $(OUT) $< -o $@ -s $(FLAG)

%.pdf: %.tex
	@latexmk $(LATEXMKOPT) -pdflatex="$(LATEX) $(LATEXOPT) %O %S" $< --silent

clean:
	@echo Cleaning...
	@latexmk -c $(TEXS)
	@rm -rf *~ *.tmp
	@rm -f *.nav *.snm *.tex *.bcf *.bbl *.blg *.aux *.end *.fls *.log *.out *.fdb_latexmk *.xml *.gz *.vrb

debug:
	@latexmk $(LATEXMKOPT) -pdflatex="$(LATEX) $(LATEXOPT) %O %S" $<

.PHONY: all watch clean debug

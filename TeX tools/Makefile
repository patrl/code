# Sourcefiles
MEXT=md
SRCS=$(wildcard *.$(MEXT))
PDFS=$(SRCS:.$(MEXT)=.pdf)
TEXS=$(SRCS:.$(MEXT)=.tex)

# Latexmk/pandoc options
LATEXMKOPT=-pdf
LATEX=pdflatex
LATEXOPT=--shell-escape
OUT=latex
FLAG=

all:	$(PDFS) $(TEXS)

%.tex: %.$(MEXT)
	@echo pandoc $<...
	@pandoc -t $(OUT) $< -o $@ -s $(FLAG)

%.pdf: %.tex
	@echo latexmk $<...
	@latexmk $(LATEXMKOPT) -pdflatex="$(LATEX) $(LATEXOPT) %O %S" $< --silent

watch: $(SRCS)
	@echo Watching for changes...
	@fswatch -0 $^ | xargs -0 -n1 sh -c 'ALT=`basename "$$1"`; make $${ALT/."$(MEXT)"/.pdf}' _

clean:
	@echo Cleaning...
	@latexmk -c $(TEXS) -f
	@rm -rf *~ *.tmp
	@rm -f *.tex *.nav *.snm *.bcf *.bbl *.blg *.aux *.end *.fls *.log *.out *.fdb_latexmk *.xml *.gz *.vrb *.aux.copy *.auxlock *.for

debug:
	@echo Debugging...
	@latexmk $(LATEXMKOPT) -pdflatex="$(LATEX) $(LATEXOPT) %O %S" $<

.PHONY: all watch clean debug

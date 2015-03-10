
COQC=coqc
COQDOC=coqdoc
DVIPDF=dvipdf

all: main doc

main:
	$(COQC) stdlib_Type.v int_comp_noquant.v int_comp.v class_comp_cbn_noquant.v class_comp_cbv.v

doc:
	$(COQDOC) -d html -g --utf8 --toc --no-index *.v

doc-pdf:
	$(COQDOC) -p "\usepackage{hyperref}\hypersetup{colorlinks=true,linkcolor=red}" -o kripke_completeness.dvi --dvi -toc -g *.v
	$(DVIPDF) kripke_completeness.dvi

clean:
	rm -f *.vo *.glob html/class*.html html/int*.html html/std*.html html/coqdoc.css html/toc.html *.dvi *.pdf


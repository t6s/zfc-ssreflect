
COQC=coqc
COQDOC=coqdoc
DVIPDF=dvipdf

all: main doc
	coqc lists.v filters.v classcomp.v

main: pairing
	coqc lists.v filters.v classcomp.v

pairing: force_look
	cd pairing; coqc extEqualNat.v misc.v primRec.v cPair.v

doc:
	$(COQDOC) -d html -g --utf8 --toc --no-index *.v pairing/*.v

doc-pdf:
	$(COQDOC) -p "\usepackage{hyperref}\hypersetup{colorlinks=true,linkcolor=red}" -o boolean_completeness.dvi --dvi -toc -g *.v pairing/*.v
	$(DVIPDF) boolean_completeness.dvi

clean:
	rm -f *.vo *.glob pairing/*.vo pairing/*.glob html/pairing*.html html/classcomp.html html/filters.html html/lists.html html/toc.html html/coqdoc.css *.dvi *.pdf

force_look:
	true

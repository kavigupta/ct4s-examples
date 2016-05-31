.ONESHELL:
filename = ct4s-companion-notes

target: coq clean notes

notes:
	pdflatex $(filename).tex
	rm $(filename).log $(filename).aux

coq:
	cd src
	coqc Category.v
	coqc FullSubcat.v
	coqc SetCategory.v
	coqc FinCategory.v
	coqc Monoid.v
	coqc MonCat.v
	coqc Group.v
	coqc Preorder.v
	coqc PreorderJoin.v
	coqc UnitNatMorph.v
	coqc LinearOrder.v
	coqc Graph.v
	coqc GraphCat.v
	coqc Isomorphism.v
	coqc IsomorphismSetGrph.v
	coqc Equivalence.v
	coqc IsoEquiv.v
	cd ..

clean:
	cd src
	rm *.glob
	rm *.vo
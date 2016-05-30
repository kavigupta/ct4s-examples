.ONESHELL:
filename = ct4s-companion-notes

notes:
	pdflatex $(filename).tex
	rm $(filename).log $(filename).aux

coq:
	cd src
	coqc category.v
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
	cd ..

clean:
	cd src
	rm *.glob
	rm *.vo
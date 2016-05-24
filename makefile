.ONESHELL:
filename = ct4s-companion-notes

notes:
	pdflatex $(filename).tex
	rm $(filename).log $(filename).aux

coq:
	cd src
	coqc category.v
	coqc SetCategory.v
	coqc FinCategory.v
	coqc Monoid.v
	coqc MonCat.v
	coqc Group.v
	coqc Preorder.v
	coqc UnitNatMorph.v
	cd ..

clean:
	cd src
	rm *.glob
	rm *.vo
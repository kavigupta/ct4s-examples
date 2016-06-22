.ONESHELL:
filename = ct4s-companion-notes

target:
	make coq
	make clean
	make notes

notes:
	pdflatex $(filename).tex
	rm $(filename).log $(filename).aux

coq:
	cd src
	coqc Category.v
	coqc Functor.v
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
	coqc -R Iso Iso Iso/Isomorphism.v
	coqc -R Iso Iso Iso/IsomorphismSetGrph.v
	coqc Equivalence.v
	coqc -R Iso Iso Iso/IsoEquiv.v
	coqc Forgetful.v
	coqc ProGrphFun.v
	# coqc GrphPrOFun.v
	cd ..

clean:
	rm **/*.glob
	rm **/*.vo
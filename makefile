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
	coqc -R Cat Cat Cat/Category.v
	coqc -R Func Func Func/Functor.v
	coqc -R Cat Cat Cat/FullSubcat.v
	coqc -R Cat Cat Cat/SetCategory.v
	coqc -R Cat Cat Cat/FinCategory.v
	coqc -R Mon Mon Mon/Monoid.v
	coqc -R Mon Mon Mon/MonCat.v
	coqc -R Grp Grp Grp/Group.v
	coqc -R Pro Pro Pro/Preorder.v
	coqc -R Pro Pro Pro/PreorderJoin.v
	coqc -R Eg Eg Eg/UnitNatMorph.v
	coqc -R Pro Pro Pro/LinearOrder.v
	coqc -R Grph Grph Grph/Graph.v
	coqc -R Grph Grph Grph/GraphCat.v
	coqc -R Iso Iso Iso/Isomorphism.v
	coqc -R Iso Iso Iso/IsomorphismSetGrph.v
	coqc -R Equiv Equiv Equiv/Equivalence.v
	coqc -R Iso Iso Iso/IsoEquiv.v
	coqc -R Func Func Func/Forgetful.v
	coqc ProGrphFun.v
	# coqc GrphPrOFun.v
	cd ..

clean:
	rm **/*.glob
	rm **/*.vo
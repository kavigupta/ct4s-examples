.ONESHELL:
filename = ct4s-companion-notes

target:
	make build
	make clean
	make notes

notes:
	pdflatex $(filename).tex
	rm $(filename).log $(filename).aux

build:
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
	coqc -R Grph Grph Grph/LinGraph.v
	coqc -R Iso Iso Iso/Isomorphism.v
	coqc -R Iso Iso Iso/IsomorphismSetGrph.v
	coqc -R Equiv Equiv Equiv/Equivalence.v
	coqc -R Iso Iso Iso/IsoEquiv.v
	coqc -R Func Func Func/Forgetful.v
	coqc -R Mon Mon Mon/FreeMonoid.v
	coqc ProGrphFun.v
	coqc GrphPrOFun.v
	coqc -R Eg Eg Eg/LinGraphPreorder.v
	coqc -R Func Func Func/FuncIso.v
	coqc -R Grph Grph Grph/Paths.v
	coqc -R Grph Grph Grph/PathsFunctor.v
	cd ..

clean:
	rm src/*.glob src/Cat/*.glob src/Eg/*.glob src/Equiv/*.glob src/Func/*.glob src/Mon/*.glob src/Grp/*.glob src/Grph/*.glob src/Iso/*.glob src/Pro/*.glob
	rm src/*.vo src/Cat/*.vo src/Eg/*.vo src/Equiv/*.vo src/Func/*.vo src/Mon/*.vo src/Grp/*.vo src/Grph/*.vo src/Iso/*.vo src/Pro/*.vo
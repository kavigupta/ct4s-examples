filename = ct4s-companion-notes

notes:
	pdflatex $(filename).tex
	rm $(filename).log $(filename).aux
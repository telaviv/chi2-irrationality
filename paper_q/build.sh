#!/bin/sh
# Build paper_q/main.pdf into paper_q/build/ (pdflatex + bibtex). Run from paper_q/.
# (no set -e: MiKTeX returns nonzero for its update reminder)
mkdir -p build
pdflatex -interaction=nonstopmode -halt-on-error -output-directory=build main.tex > build/pass1.log
cp references.bib build/
(cd build && bibtex main > bibtex.log)
pdflatex -interaction=nonstopmode -halt-on-error -output-directory=build main.tex > build/pass2.log
pdflatex -interaction=nonstopmode -halt-on-error -output-directory=build main.tex > build/pass3.log
grep -E "^!|undefined|Citation .* undefined|multiply defined" build/main.log || echo "no errors, no undefined references"
grep -c "Overfull" build/main.log || true

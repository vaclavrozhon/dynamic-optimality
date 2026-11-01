.PHONY: lean audit guide

lean:
	lake build

audit: lean
	lake env lean AuditAll.lean
	lake env lean AuditDynamicOptimality.lean

guide:
	cd docs/tango2-proof-guide && pdflatex -interaction=nonstopmode -halt-on-error guide.tex
	cd docs/tango2-proof-guide && pdflatex -interaction=nonstopmode -halt-on-error guide.tex

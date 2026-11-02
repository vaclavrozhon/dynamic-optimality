.PHONY: lean audit guide graph

lean:
	lake build

audit: lean
	lake env lean AuditAll.lean
	lake env lean AuditDynamicOptimality.lean

guide:
	cd docs/chacha-proof-guide && pdflatex -interaction=nonstopmode -halt-on-error guide.tex
	cd docs/chacha-proof-guide && pdflatex -interaction=nonstopmode -halt-on-error guide.tex

# The exporter serializes Lean work with the same lock used for audits.
graph:
	python3 tools/dependency_graph/export.py
	python3 tools/dependency_graph/build.py

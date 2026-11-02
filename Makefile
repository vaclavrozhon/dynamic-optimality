.PHONY: lean audit guide graph

lean:
	lake build

# The runner builds every registered module and audits their declarations once.
# It does not acquire a lock; callers can use the usual external flock command.
audit:
	python3 tools/audit.py

guide:
	cd docs/chacha-proof-guide && pdflatex -interaction=nonstopmode -halt-on-error guide.tex
	cd docs/chacha-proof-guide && pdflatex -interaction=nonstopmode -halt-on-error guide.tex

# The exporter serializes Lean work with the same lock used for audits.
graph:
	python3 tools/dependency_graph/export.py
	python3 tools/dependency_graph/build.py

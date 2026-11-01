# Dynamic-optimality proofs

Lean formalizations of splay, Greedy, Tango², and intermediate results for classical MultiSplay, using one shared BST type and offline optimum. This repository is a source snapshot of the shared workspace on 1 November 2026; see [provenance](docs/PROVENANCE.txt) and the [source hashes](docs/snapshots/2026-11-01.sources.sha256).

The public entry point is [DynamicOptimalityResults.lean](DynamicOptimalityResults.lean). Write `L₀(n) = n` and `Lₖ₊₁(n) = ceil(log₂(max(2, Lₖ(n))))`. These stabilized logarithms make the following factors meaningful even for small universes.

| Development | Exported competitive factor | Algorithm cost |
| --- | --- | --- |
| Splay | `L₂(n) · L₃(n)²` | Requests plus standard splay rotations. |
| Greedy | `L₂(n)` | Geometric touches, initialized from the supplied BST. |
| Tango² | `L₃(n)` | Search depth in the initial tree of each access, plus one, plus subsequent ordinary rotations. |
| MultiSplay | Intermediate results | A persistent forest comparison and actual switch-counter bounds; full competitiveness remains unfinished. |

In [DynamicOptimality.Cost](DynamicOptimality/Cost.lean), `OPT X` is the attained minimum over actual root-serving BST executions, counting requests plus rotations and allowing a freely chosen initial tree. The shared statement `Competitive cost factor` means

```text
∃ C > 0, ∀ n > 0, ∀ initial : BST 0 n, ∀ requests : List (Fin n),
  cost initial requests ≤ C * (OPT requests + n) * factor n.
```

The three completed results use this same comparison optimum, with the distinct algorithm costs shown above. Greedy's exported cost is geometric; its statement should not be read as an additional physical BST implementation theorem. Splay also has a [separate improved-factor export](DynamicOptimality/SplayBlackBoxBound.lean).

Tango² is a fixed deterministic mathematical online strategy for every finite key universe and every initial BST. Computation and bookkeeping are free, and per-state classical choices are permitted. Its actual trees contain exactly the original keys. The theorem does not assert an executable evaluator or a bounded local controller. See [TangoSquaredAll.lean](TangoSquaredAll.lean) and the [formalization map](FORMALIZATION.md).

## Build and audit

Install `elan`, then run from the repository root:

```sh
elan toolchain install leanprover/lean4:v4.32.1
lake exe cache get
lake build
make audit
```

[lean-toolchain](lean-toolchain) and [lake-manifest.json](lake-manifest.json) pin Lean and the external dependencies. Initial dependency and cache retrieval needs network access. No experimental datasets or original-workspace paths are required.

`make audit` builds the project and runs both `AuditAll.lean` and the detailed `AuditDynamicOptimality.lean`. Without Make, run those files with `lake env lean` after `lake build`. A separate Greedy audit is available as `lake env lean AuditGreedy.lean`. Run builds and audits one at a time; the full environment can require substantial memory.

## Reading the proofs

- [Current interfaces and remaining work](FORMALIZATION.md)
- [Tango² proof guide](docs/tango2-proof-guide/guide.pdf) and [LaTeX source](docs/tango2-proof-guide/guide.tex)
- [Splay proof map](splay/formalization/COMPLETED_PROOF.md)
- [Greedy proof map](greedy/formalization/README.txt)
- [Tango² mathematical repairs](tango_squared/lean/PROOF_REPAIRS_2026_10_30.md)
- [MultiSplay composition audit](multisplay/composition-audit.tex) and [proposed comparator](multisplay/tango-common-forest-comparator.tex)

`make guide` rebuilds the guide with pdfLaTeX and standard TeX packages, including TikZ.

No license has yet been selected for this repository. Dependency licenses do not determine the license of these sources. The original [splay Git history](https://github.com/vaclavrozhon/splay) remains separate; this snapshot includes substantial later work.

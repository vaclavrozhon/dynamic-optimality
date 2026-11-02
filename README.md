# Dynamic optimality in Lean

Machine-checked competitive bounds for **Splay, Greedy, Cha-Cha, and classical MultiSplay**, built on one shared binary search tree model and offline optimum.

Dynamic optimality asks whether an online binary search tree can serve every request sequence within a constant factor of the best algorithm that knows the whole sequence in advance. This repository proves the bounds below, which still depend on the number of keys. It also formalizes the tree operations, initialization, and supporting equivalences between five cost models.

Start with [the public theorem statements](DynamicOptimalityResults.lean), or read the [formalization map](FORMALIZATION.md) for the definitions and proof dependencies. The main source papers are [*Splay trees are almost dynamically optimal*](https://arxiv.org/abs/2607.18498) and the forthcoming public manuscript [*Dynamic Optimality to within O(log log log n)*](#chacha2026). Full references and [BibTeX entries](docs/references.bib) appear below.

The [interactive dependency graph](https://vaclavrozhon.github.io/dynamic-optimality/proof-atlas.html) lets you explore all repository declarations and their direct references, with a spring layout, module overview, and searchable theorem neighborhoods. The [project page](https://vaclavrozhon.github.io/dynamic-optimality/) introduces the results and references. You can also [download the standalone HTML](https://github.com/vaclavrozhon/dynamic-optimality/raw/refs/heads/main/docs/dependency-graph.html) for offline use. See the [graph guide](docs/DEPENDENCY_GRAPH.md) for controls and rebuilding.

## What is proved

Let `n` be the number of keys and `X` a finite sequence of successful searches. `OPT(X)` is the minimum cost of an offline BST execution, with a freely chosen initial tree; it charges one unit per request and one per ordinary rotation, and brings each requested key to the root. Every algorithm bound has the form

```text
cost(initial, X) ≤ C · (OPT(X) + n) · factor(n),
```

where one constant `C > 0` works for every `n > 0`, every supplied initial tree, and every request sequence. The additive `n` pays for initialization. This is the shared Lean predicate [`Competitive`](DynamicOptimality/Cost.lean).

Write `L₀(n) = n` and `Lₖ₊₁(n) = ceil(log₂(max(2, Lₖ(n))))`. These stabilized iterated logarithms remain positive on small universes: `L₂` corresponds to log log and `L₃` to log log log. The refined Splay factor is `g(n) = L₂(n) · L₃(n) · E(24 · L₂(n))`, where `E` is an explicit slowly growing function of the number of repeated logarithms needed to reach two. Its [full definition](#refined-splay-factor) is given below.

| Algorithm | Proved competitive factor | Charged algorithm cost |
| --- | --- | --- |
| **Splay** | `L₂(n) · L₃(n)²`, and the refined factor `g(n)` | Requests plus standard splay rotations. |
| **Greedy** | `L₂(n)` | Geometric touches, initialized from the supplied BST. |
| **Cha-Cha** | `L₃(n)` | Search depth before each access, plus one, plus ordinary rotations. |
| **Classical MultiSplay** | `L₃(n) · g(ceil(log₂(n+1)))` | Search depth before each access, plus one, plus ordinary rotations. |

### Splay and Greedy

The **Splay** theorem concerns the usual splay algorithm and its actual rotations. The simpler factor is the bound stated in [Chmel et al., *Splay trees are almost dynamically optimal*](#splay2026). The repository also exports the refined factor through [`splay_eg_competitive`](DynamicOptimality/SplayBlackBoxBound.lean). See the [Splay proof map](splay/formalization/COMPLETED_PROOF.md).

The **Greedy** theorem concerns the geometric algorithm: a touch is a key–time point, and cost is the number of touches. Its actual rows satisfy the rectangle condition defining valid geometric executions, and a [fixed online geometric strategy](DynamicOptimality/GeometricOnlineGreedy.lean) reproduces those rows and their exact cost. The current result does not include an online physical BST implementation of Greedy. The [Greedy proof map](greedy/formalization/README.txt) explains the bound. The related paper [Guo et al.](#greedy2026) proves a different bound, `2^{O(√(log log n))}`; the stronger `O(log log n)` statement here is a repository result, not a claim attributed to that paper.

### Cha-Cha

The source is [Čech et al., *Dynamic Optimality to within O(log log log n)*](#chacha2026), an unpublished manuscript whose public version is forthcoming. Its algorithm is called **Cha-Cha**, and the Lean library uses the name `ChaCha`.

[`ChaChaAll.lean`](ChaChaAll.lean) exports one fixed deterministic online BST strategy for every finite key universe and every supplied initial tree. Its physical trees contain exactly the original keys; its execution theorem certifies actual searches and ordinary rotations. Initialization is charged once. The final competitive theorem has no unproved implementation or lower-bound premise.

The [proof guide](docs/chacha-proof-guide/guide.pdf) connects the argument to Lean. The [repair notes](chacha/lean/PROOF_REPAIRS_2026_10_30.md) record mathematical corrections and differences from the imported manuscript.

### Classical MultiSplay

The [MultiSplay theorem](multisplay/lean/MultiSplay/CompetitiveLogHeight.lean) uses the classical algorithm of [Wang, Derryberry, and Sleator](#multisplay2006), including its bottom-up switch order and final switch. It proves

```text
cost(initial, X) = O((OPT(X) + n) · L₃(n) · g(ceil(log₂(n+1)))).
```

The proof constructs the comparison algorithm used for the persistent forest of splay components. No cheap-comparator or physical-simulation assumption remains in the concrete result. The [composed proof](multisplay/COMPOSED_BOUND.txt) explains how the Splay analysis and the Cha-Cha comparison fit together.

A generic theorem also works for any monotone factor satisfying `AdmissibleForestFactor`: this means that the factor uniformly bounds the coefficients of the proved Splay interface for persistent searches, splits, and joins. A competitiveness theorem for searches alone is not sufficient for that interface. See `competitive_generic_logarithmic` in the [final module](multisplay/lean/MultiSplay/CompetitiveLogHeight.lean).

### Refined Splay factor

The factor used in the MultiSplay composition is exactly

```text
g(n) = L₂(n) · L₃(n) · E(24 · L₂(n)).
```

Here `E(G)` bounds the coefficients accumulated by repeated logarithmic compression. Let `d(G)` be the number of iterations of `G ↦ ceil(log₂(G))` needed to reach a value at most two. Then

```text
E(G) = (2^(20 · (d(G) + 1)) · ((d(G) + 1)!)²)².
```

These are the definitions [`egTargetFactor`](splay/formalization/Splay/Accounting/IteratedLogEGBound.lean) and [`LayerEnvelope.E`](splay/formalization/Splay/Analysis/LayerEnvelope.lean). The factor retains the full coefficient dependence; there is no hidden constant depending on the number of compression levels.

## Model and scope

All results concern successful searches on a fixed finite ordered key set. The mathematical BST model permits free computation and bookkeeping. Cha-Cha and MultiSplay use fixed per-state classical choices, so their online strategies depend only on the current state and request, but the formalization does not assert an executable evaluator or a bounded local controller. Their initial and final physical trees and rotation costs are certified.

As supporting results, [`BSTModels.lean`](DynamicOptimality/BSTModels.lean) proves finite cost equivalence of five models:

1. **Root serving:** bring each request to the root; charge requests and rotations.
2. **Search and rotations:** charge the initial search depth plus one and subsequent rotations.
3. **Single pointer:** start each request at the root; charge each adjacent move, local rotation, and request service.
4. **Rooted subtree:** rearrange a connected subtree containing the root and requested key; charge its number of keys.
5. **Geometry:** charge points in an arborally satisfied set—every rectangle spanned by two points with different keys and times contains a third point, including its boundary.

For all 25 ordered pairs, a finite execution has a corresponding execution with cost at most **481 times** its cost. The constant is uniform; initial trees may be freely chosen. Rooted-subtree and geometric executions have exactly the same attainable costs. The geometric formulation follows [Demaine et al.](#geometry2009) and assumes no BST witness.

Online conversions among the four tree models and from trees to geometry are also proved. **The converse conversion of an arbitrary online geometric strategy to an online BST is a separate, unfinished task.** The finite geometric reconstruction does not claim this stronger result. See the [model guide](docs/BST_MODELS.txt) for constants, initialization, and exact statements.

## Build and check the proofs

Install `elan`, then run from the repository root:

```sh
elan toolchain install leanprover/lean4:v4.32.1
lake exe cache get
make audit
```

The [toolchain](lean-toolchain) and [Lake manifest](lake-manifest.json) pin Lean and its dependencies. Initial dependency and cache retrieval requires network access. No original-workspace paths or experimental datasets are needed.

`make audit` builds the project and runs [AuditAll.lean](AuditAll.lean) and [AuditDynamicOptimality.lean](AuditDynamicOptimality.lean). These inspect logical dependencies, including private declarations. The accepted axioms are `propext`, `Classical.choice`, and `Quot.sound`; proof gaps such as `sorry` are not accepted. A separate focused Greedy audit is available as `lake env lean AuditGreedy.lean`. Run builds and audits one at a time; the full environment can require substantial memory.

The full build and both audits passed on 1 November 2026, including the five-model equivalence; see the [verification record](docs/verification-bst-models.txt).

For navigation, use the [formalization map](FORMALIZATION.md), [public entry point](DynamicOptimalityResults.lean), and proof guides linked above. `make guide` rebuilds the Cha-Cha guide with pdfLaTeX and standard TeX packages, including TikZ.

## References

The following distinguish source papers, algorithm definitions, and related work. The Lean statements linked above specify exactly what this repository proves. Reusable entries are in [references.bib](docs/references.bib).

<a id="splay2026"></a>
**Splay analysis.** Petr Chmel, Bernhard Haeupler, Richard Hladík, Michal Koucký, Antti Roeyskoe, Václav Rozhoň, Ondřej Sladký, and Robert E. Tarjan. *Splay trees are almost dynamically optimal*. 2026. [arXiv:2607.18498](https://arxiv.org/abs/2607.18498).

<a id="chacha2026"></a>
**Cha-Cha analysis.** Daniel Čech, Bernhard Haeupler, Antti Roeyskoe, Václav Rozhoň, Robert E. Tarjan, and Sorrachai Yingchareonthawornchai. *Dynamic Optimality to within O(log log log n)*. Unpublished manuscript, 2026. **Public version forthcoming.**

<a id="greedy2026"></a>
**Related Greedy analysis.** Yuhao Guo, Seth Pettie, Daniel Skora, and Chengzhang Wan. *The Greedy Binary Search Tree is Non-trivially Competitive*. 2026. [arXiv:2608.04410](https://arxiv.org/abs/2608.04410).

<a id="multisplay2006"></a>
**Classical MultiSplay.** Chengwen Chris Wang, Jonathan Derryberry, and Daniel Dominic Sleator. *O(log log n)-Competitive Dynamic Binary Search Trees*. SODA 2006, pp. 374–383. [Paper](https://www.cs.cmu.edu/~jonderry/multi-splay.pdf).

<a id="geometry2009"></a>
**Geometric BST model.** Erik D. Demaine, Dion Harmon, John Iacono, Daniel Kane, and Mihai Pătraşcu. *The Geometry of Binary Search Trees*. SODA 2009, pp. 496–505. [Paper and publication details](https://erikdemaine.org/papers/BST_SODA2009/).

**Tango trees.** Erik D. Demaine, Dion Harmon, John Iacono, and Mihai Pătraşcu. *Dynamic Optimality—Almost*. SIAM Journal on Computing 37(1), 2007, pp. 240–251. [Paper and publication details](https://erikdemaine.org/papers/Tango_SICOMP/).

**Original Splay algorithm.** Daniel Dominic Sleator and Robert Endre Tarjan. *Self-Adjusting Binary Search Trees*. Journal of the ACM 32(3), 1985, pp. 652–686. [Paper](https://www.cs.cmu.edu/~sleator/papers/Self-Adjusting.htm).

## Source history

This repository began with a source snapshot of the shared workspace on 1 November 2026. The original [splay Git history](https://github.com/vaclavrozhon/splay) remains separate; this repository includes substantial later work. See [provenance](docs/PROVENANCE.txt) and the [current source hashes](docs/snapshots/2026-11-02.sources.sha256).

No license has yet been selected for this repository. Dependency licenses do not determine the license of these sources.

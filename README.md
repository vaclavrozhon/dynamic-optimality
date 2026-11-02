# Dynamic optimality in Lean

Machine-checked competitive bounds for **Splay, Greedy, Cha-Cha, and classical MultiSplay**, built on one shared binary search tree model and offline optimum.

Dynamic optimality asks whether an online binary search tree can serve every request sequence within a constant factor of the best algorithm that knows the whole sequence in advance. This repository proves the bounds below, which still depend on the number of keys. It also formalizes the tree operations, initialization, and supporting equivalences between five cost models.

Start with [the public theorem statements](DynamicOptimalityResults.lean), or read the [formalization map](FORMALIZATION.md) for the definitions and proof dependencies. The main source papers are [*Splay trees are almost dynamically optimal*](https://arxiv.org/abs/2607.18498) and the forthcoming public manuscript [*Dynamic Optimality to within O(log log log n)*](#chacha2026). Full references and [BibTeX entries](docs/references.bib) appear below.

The [interactive dependency graph](https://vaclavrozhon.github.io/dynamic-optimality/proof-atlas.html) lets you switch between modules and individual declarations. The main results are marked with stars and have direct navigation buttons. Zoom with the wheel or the zoom buttons; hover over a node to highlight its dependencies. The [project page](https://vaclavrozhon.github.io/dynamic-optimality/) introduces the results and references. You can also [download the standalone HTML](https://github.com/vaclavrozhon/dynamic-optimality/raw/refs/heads/main/docs/dependency-graph.html) for offline use. See the [graph guide](docs/DEPENDENCY_GRAPH.md) for controls and rebuilding.

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
| **Greedy** | `L₂(n)` | Geometric touches, with a proved online physical BST simulation within a constant factor. |
| **Cha-Cha** | `L₃(n)` | Search depth before each access, plus one, plus ordinary rotations. |
| **Cha-Cha with Splay auxiliaries** | `L₃(n)` | The same physical BST cost, with ordinary bottom-up Splay inside the maintained components. |
| **Classical MultiSplay** | `L₃(n) · g(ceil(log₂(n+1)))` | Search depth before each access, plus one, plus ordinary rotations. |

### Splay and Greedy

The **Splay** theorem concerns the usual splay algorithm and its actual rotations. The simpler factor is the bound stated in [Chmel et al., *Splay trees are almost dynamically optimal*](#splay2026). The common entry point exports the refined factor as [`Results.splay_refined`](DynamicOptimalityResults.lean); the original [`splay_eg_competitive`](DynamicOptimality/SplayBlackBoxBound.lean) name is also retained. See the [Splay proof map](splay/formalization/COMPLETED_PROOF.md).

The **Greedy** theorem concerns the geometric algorithm: a touch is a key–time point, and cost is the number of touches. Its actual rows satisfy the rectangle condition defining valid geometric executions, and a [fixed online geometric strategy](DynamicOptimality/GeometricOnlineGreedy.lean) reproduces those rows and their exact cost. The [physical simulation](DynamicOptimality/GeometricOnlineSimulation/GreedyInstance.lean) supplies one online BST with cost at most `381 · Greedy.cost + 387n`, on the original keys and from any supplied initial tree. Greedy's reference initialization is fixed before all request words. The [Greedy proof map](greedy/formalization/README.txt) explains the competitive bound. The related paper [Guo et al.](#greedy2026) proves a different bound, `2^{O(√(log log n))}`; the stronger `O(log log n)` statement here is a repository result, not a claim attributed to that paper.

### Cha-Cha

The source is [Čech et al., *Dynamic Optimality to within O(log log log n)*](#chacha2026), an unpublished manuscript whose public version is forthcoming. Its algorithm is called **Cha-Cha**, and the Lean library uses the name `ChaCha`.

[`ChaChaAll.lean`](ChaChaAll.lean) exports one fixed deterministic online BST strategy for every finite key universe and every supplied initial tree. Its physical trees contain exactly the original keys; its execution theorem certifies actual searches and ordinary rotations. Initialization is charged once. The final competitive theorem has no unproved implementation or lower-bound premise.

The [proof guide](docs/chacha-proof-guide/guide.pdf) connects the argument to Lean. The [repair notes](chacha/lean/PROOF_REPAIRS_2026_10_30.md) record mathematical corrections and differences from the imported manuscript.

The same `L₃(n)` bound is now proved for **Cha-Cha with ordinary Splay auxiliary trees**, exported as [`Results.chacha_splay`](DynamicOptimalityResults.lean). Its [complete implementation and bound](chacha/lean/ChaCha/Paper20261030/SplayAuxiliaryAll.lean) retain the ordinary Splay operations and persistent component shapes. For arbitrary universe sizes, the ordinary-operation certificate applies to the padded auxiliary bookkeeping; projection realizes its rotations physically on the original keys. The projection is not asserted to be literal Splay on each pruned component. This is the two-level Cha-Cha construction; the classical MultiSplay theorem below concerns its own switch schedule and has a different bound.

### Classical MultiSplay

The [MultiSplay theorem](multisplay/lean/MultiSplay/CompetitiveLogHeight.lean) uses the classical algorithm of [Wang, Derryberry, and Sleator](#multisplay2006), including its bottom-up switch order and final switch. It proves

```text
cost(initial, X) = O((OPT(X) + n) · L₃(n) · g(ceil(log₂(n+1)))).
```

The proof constructs the comparison algorithm used for the persistent forest of splay components. No cheap-comparator or physical-simulation assumption remains in the concrete result. The [composed proof](multisplay/COMPOSED_BOUND.txt) explains how the Splay analysis and the Cha-Cha comparison fit together.

A generic theorem also works for any monotone factor satisfying `AdmissibleForestFactor`: this means that the factor uniformly bounds the coefficients of the proved Splay interface for persistent searches, splits, and joins. A competitiveness theorem for searches alone is not sufficient for that interface. The concrete result specializes this generic theorem using the proved instance [`admissible_egTargetFactor`](multisplay/lean/MultiSplay/GlobalPreferredGenericBound.lean). See `competitive_generic_logarithmic` in the [final module](multisplay/lean/MultiSplay/CompetitiveLogHeight.lean).

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

## Further bounds and structural results

The **explicit lower-bound separation** evaluates two quantities on the same repeated bit-reversal request sequence. Write `m` for its length, `P` for primary-reference alternations, `D` for depth-reference alternations, and `R` for the robust rectangle bound. For `F₀ = m + P + D`, the [checked family](chacha/lean/ChaCha/Separation/Explicit.lean) satisfies

```text
m ≤ F₀ ≤ 4m,
L₃(n) · F₀ ≤ 8R,     R ≤ 4 · L₃(n) · F₀.
```

Thus the robust bound can exceed the original length-plus-alternation bound by a factor `Θ(L₃(n))`. The [construction notes](docs/separation-formalization-notes.txt) give the exact keys and reference trees and explain the small parameter change from the manuscript.

The [entropy residual theorem](docs/entropy-residual.txt) strengthens the fixed-reference alternation counter. At each request time, it takes the larger of the original primary-plus-depth event count and the event count from an additional ordered reference tree; the request itself contributes one. The resulting counter `F_res` satisfies `F_res(X) ≤ 519·OPT(X)` for every ordering. One additional reference chosen only from the key frequencies also satisfies

```text
E[F_res(X)] ≥ m·(1+H)/(2·log₂(3)),
```

where `H = −Σₓ pₓ log₂(pₓ)` is the entropy of the key frequencies `pₓ`. The expectation is over uniformly random words with those same frequencies. The formalization constructs this probability distribution and the auxiliary reference; the entropy assertion is an expectation bound, not a lower bound for every individual ordering.

For **shuffles of `k` nearest-neighbor walks**, each source walks on a fixed ordered subset, staying put or moving to its preceding or following key. The subsets may overlap and the interleaving may be arbitrary. With `m` total requests and `λ(k) = 1 + floor(log₂(k+1))`, [`Results.colored_shuffle`](DynamicOptimalityResults.lean) proves

```text
OPT(X) ≤ 292864 · m · λ(k)².
```

The proof constructs a static colored BST, simulates its persistent fingers by actual ordinary rotations, and projects overlapping colored copies back to the original keys. The optimum bound has no additive `n`; an actual execution from any supplied initial BST costs at most twice this bound plus `12n`. The [proof guide](docs/colored-walks.txt) explains both logarithms and the connection to the multiple-finger simulation of [Chalermsook et al.](#multifinger2018). This is an offline optimum bound for fixed subsets.

The **funnel count** `F(X)` counts left-to-right changes among the earlier occurrences visible from each request through empty closed rectangles. Occurrences at repeated keys remain distinct. For every occurrence-preserving shuffle `W` of two words `X` and `Y`, the [shuffle theorem](DynamicOptimality/Funnel/ShuffleOPT.lean) proves

```text
F(W) + |W| ≤ 360639 · (OPT(X) + OPT(Y)).
```

The source alphabets may overlap, and there is no additive universe-size allowance. If keys are partitioned into consecutive intervals, let `template` replace every request by its interval label and let `partᵢ` retain the requests in interval `i`. The [convex-composition theorem](DynamicOptimality/Funnel/ConvexComposition.lean) proves

```text
F(W) ≤ F(template) + Σᵢ F(partᵢ) + 9|W|.
```

The proof also formalizes the approximate monotonicity argument of [Levy and Tarjan, Section 7](#levytarjan2022): deleting occurrences gives `F(subsequence) ≤ 4F(sequence) + 8|sequence|`.

Two structural results support comparisons between BST executions. [Rowwise nearest-common-ancestor closure](DynamicOptimality/ReferenceClosure.lean) in any fixed reference BST preserves arboral satisfaction; a nonempty row of `r` keys grows to at most `2r−1` keys. The union of the rows in any closed time interval is also closed under nearest common ancestors. The [comparison normal form](splay/formalization/Splay/Accounting/LogHeightNormalForm.lean) constructs an actual execution of cost `O(OPT+n)` whose intermediate trees all have height `O(log(n+1))`, whose rotations occur at depth at most one, and whose minor ribs have length at most 20. A minor rib follows one left edge and then only right edges, or one right edge and then only left edges, ending at the adjacent null position.

Two [MultiSplay counterexamples](docs/multisplay-obstructions.txt) record limitations of possible proof arguments. Ordinary Splay does not commute with interval restriction. A second, unbounded family of actual physical accesses refutes a specified per-request bound using the classical sum-of-logarithms potential, even after adding any function of the primary preferred forest. The family starts from legal supplied states; it does not assert a competitive lower bound or contradict the composed MultiSplay theorem.

## Model and scope

All results concern successful searches on a fixed finite ordered key set. The mathematical BST model permits free computation and bookkeeping. Cha-Cha and MultiSplay use fixed per-state classical choices, so their online strategies depend only on the current state and request, but the formalization does not assert an executable evaluator or a bounded local controller. Their initial and final physical trees and rotation costs are certified.

As supporting results, [`BSTModels.lean`](DynamicOptimality/BSTModels.lean) proves finite cost equivalence of five models:

1. **Root serving:** bring each request to the root; charge requests and rotations.
2. **Search and rotations:** charge the initial search depth plus one and subsequent rotations.
3. **Single pointer:** start each request at the root; charge each adjacent move, local rotation, and request service.
4. **Rooted subtree:** rearrange a connected subtree containing the root and requested key; charge its number of keys.
5. **Geometry:** charge points in an arborally satisfied set—every rectangle spanned by two points with different keys and times contains a third point, including its boundary.

For all 25 ordered pairs, a finite execution has a corresponding execution with cost at most **481 times** its cost. The constant is uniform; initial trees may be freely chosen. Rooted-subtree and geometric executions have exactly the same attainable costs. The geometric formulation follows [Demaine et al.](#geometry2009) and assumes no BST witness.

Online conversions among the four tree models and both directions between trees and geometry are also proved. For any online geometric strategy from the standard free baseline, [`Results.geometric_online`](DynamicOptimalityResults.lean) fixes one physical BST strategy before future requests and proves `BST cost ≤ 381 · geometric cost + 387n` simultaneously for every prefix. The additive term pays initialization from the supplied BST once. The [online construction guide](docs/geometric-online-simulation.txt) explains its actual split trees and rotations; the [model guide](docs/BST_MODELS.txt) records all five interfaces and their constants.

## Build and check the proofs

Install `elan`, then run from the repository root:

```sh
elan toolchain install leanprover/lean4:v4.32.1
lake exe cache get
make audit
```

The [toolchain](lean-toolchain) and [Lake manifest](lake-manifest.json) pin Lean and its dependencies. Initial dependency and cache retrieval requires network access. No original-workspace paths or experimental datasets are needed.

`make audit` builds every tracked Lean module registered in the Lake configuration, then checks the logical dependencies of every declaration originating in those modules, including private and generated declarations. It also runs the explicit endpoint checks listed in [AuditAll.lean](AuditAll.lean) and [AuditDynamicOptimality.lean](AuditDynamicOptimality.lean). The accepted axioms are `propext`, `Classical.choice`, and `Quot.sound`; proof gaps such as `sorry` are not accepted. The [audit runner](tools/audit.py) verifies module coverage before checking axioms. The original root audit files remain available as narrower checks; `lake env lean AuditGreedy.lean` focuses on Greedy. Run builds and audits one at a time; the full environment can require substantial memory.

The full build and expanded audit passed on 2 November 2026 after adding the further bounds and causal simulations: all 2,507 registered modules built, and all 69,472 local declarations used only the accepted axioms. The audit also checked 406 explicit endpoints. See the [verification record](docs/verification-additional-2026-11-02.txt), [additional results](docs/additional-formalization-2026-11-02.txt), and [semantic review](docs/additional-review-2026-11-02.txt). The [earlier review](docs/review-2026-11-02.txt) records the preceding MultiSplay refactor. The earlier [five-model verification](docs/verification-bst-models.txt) records the supporting equivalences. [GitHub Actions](https://github.com/vaclavrozhon/dynamic-optimality/actions/workflows/lean.yml) repeats the full registered-module build and audit on future pushes.

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

<a id="levytarjan2022"></a>
**Approximate monotonicity of the funnel bound.** Caleb C. Levy and Robert E. Tarjan. *A Foundation for Proving Splay is Dynamically Optimal*. arXiv:1907.06310, version 3, 2022, Section 7. [Manuscript](https://arxiv.org/abs/1907.06310v3).

<a id="multifinger2018"></a>
**Simulation of multiple fingers.** Parinya Chalermsook, Mayank Goswami, László Kozma, Kurt Mehlhorn, and Thatchaphol Saranurak. *Multi-Finger Binary Search Trees*. ISAAC 2018, LIPIcs 123, pp. 55:1–55:26. [Paper and publication details](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ISAAC.2018.55).

**Tango trees.** Erik D. Demaine, Dion Harmon, John Iacono, and Mihai Pătraşcu. *Dynamic Optimality—Almost*. SIAM Journal on Computing 37(1), 2007, pp. 240–251. [Paper and publication details](https://erikdemaine.org/papers/Tango_SICOMP/).

**Original Splay algorithm.** Daniel Dominic Sleator and Robert Endre Tarjan. *Self-Adjusting Binary Search Trees*. Journal of the ACM 32(3), 1985, pp. 652–686. [Paper](https://www.cs.cmu.edu/~sleator/papers/Self-Adjusting.htm).

## Source history

This repository began with a source snapshot of the shared workspace on 1 November 2026. The original [splay Git history](https://github.com/vaclavrozhon/splay) remains separate; this repository includes substantial later work. See [provenance](docs/PROVENANCE.txt) and the [current source hashes](docs/snapshots/2026-11-02.review.sources.sha256).

No license has yet been selected for this repository. Dependency licenses do not determine the license of these sources.

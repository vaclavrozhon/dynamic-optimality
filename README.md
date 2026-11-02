# Dynamic optimality in Lean

**Machine-checked competitive bounds for Splay, Greedy, Cha-Cha, and classical MultiSplay**, sharing one binary search tree model and one offline optimum.

Dynamic optimality asks whether an online binary search tree can serve every search sequence within a constant factor of the best algorithm that knows the future. This library proves bounds approaching that goal, together with the tree constructions, lower bounds, and simulations that support them. The factors still depend on the number of keys; constant-factor dynamic optimality remains open.

[**Main results**](#what-is-proved) · [**Lean statements**](DynamicOptimalityResults.lean) · [**Interactive proof graph**](https://vaclavrozhon.github.io/dynamic-optimality/proof-atlas.html) · [**Build the proofs**](#build-and-check-the-proofs) · [**References**](#references)

The main source papers are [*Splay trees are almost dynamically optimal*](#splay2026) and [*Dynamic Optimality to within O(log log log n)*](#chacha2026), whose public manuscript is forthcoming. The [formalization map](FORMALIZATION.md) connects the mathematical statements to their definitions and proofs.

## What is proved

Let `n` be the number of keys and `X` a finite sequence of successful searches. The shared **offline optimum**, `OPT(X)`, minimizes the number of requests plus ordinary rotations over executions that bring each requested key to the root. It may choose its initial tree with knowledge of the entire sequence.

Each competitive theorem has the form

```text
cost(initial, X) ≤ C · (OPT(X) + n) · factor(n).
```

One constant `C > 0` works for every `n > 0`, every supplied initial tree, and every request sequence. The additive `n` pays for initialization once. This is the Lean predicate [`Competitive`](DynamicOptimality/Cost.lean).

For precise bounds, use the stabilized iterated logarithms

```text
L₀(n) = n,       Lₖ₊₁(n) = ceil(log₂(max(2, Lₖ(n)))).
```

Thus `L₂` corresponds to log log and `L₃` to log log log, with positive values even on small universes. The refined Splay factor `g` is defined immediately below the table.

| Algorithm | Proved competitive factor | Public Lean theorem |
| --- | --- | --- |
| **Splay** | `L₂(n) · L₃(n)²` | `Results.splay` |
| **Splay, refined bound** | `g(n)` | `Results.splay_refined` |
| **Greedy** | `L₂(n)` | `Results.greedy` |
| **Cha-Cha** | `L₃(n)` | `Results.chacha` |
| **Cha-Cha with Splay auxiliaries** | `L₃(n)` | `Results.chacha_splay` |
| **Classical MultiSplay** | `L₃(n) · g(ceil(log₂(n+1)))` | `Results.multisplay` |

All six statements are in [`DynamicOptimalityResults.lean`](DynamicOptimalityResults.lean), under the namespace `DynamicOptimality.Results`.

Splay's cost counts requests and its standard rotations. Cha-Cha and MultiSplay charge the requested key's **initial search depth plus one, then ordinary rotations**. Greedy counts geometric touches—key–time points—and has a proved online simulation by physical BST rotations. A row is the set of keys touched at one time. These costs are compared with the same `OPT`; the [model equivalences](#model-and-scope) justify transferring bounds between conventions.

### Refined Splay factor

The exact function used both for Splay and inside the MultiSplay composition is

```text
g(n) = L₂(n) · L₃(n) · E(24 · L₂(n)).
```

The function `E` records the coefficients accumulated by repeatedly compressing a size parameter logarithmically. Let `d(G)` count the iterations of `G ↦ ceil(log₂(G))` needed to reach a value at most two, with `d(G) = 0` when `G ≤ 2`. Then

```text
E(G) = (2^(20 · (d(G) + 1)) · ((d(G) + 1)!)²)².
```

Here `!` denotes factorial. The extra factor therefore depends only on an iterated-logarithm depth, rather than on the original universe size directly. All of that dependence is explicit in [`egTargetFactor`](splay/formalization/Splay/Accounting/IteratedLogEGBound.lean) and [`LayerEnvelope.E`](splay/formalization/Splay/Analysis/LayerEnvelope.lean); no constant is allowed to depend on the number of compression levels.

### Splay and Greedy

**Splay.** The proofs analyze the usual bottom-up splay algorithm and its actual rotations. They establish both the bound in [Chmel et al.](#splay2026) and the refined factor above. The [Splay proof map](splay/formalization/COMPLETED_PROOF.md) explains the route from the access analysis to the final competitive theorem.

**Greedy.** The geometric algorithm's actual touch rows form a valid geometric execution. A [fixed online strategy](DynamicOptimality/GeometricOnlineGreedy.lean) reproduces those rows and their exact cost. Its [physical BST simulation](DynamicOptimality/GeometricOnlineSimulation/GreedyInstance.lean), on the original keys and from any supplied physical initial tree, costs at most

```text
381 · Greedy.cost + 387n.
```

The geometric reference initialization is fixed before all request sequences. The [Greedy proof map](greedy/formalization/README.txt) describes the competitive analysis. The related paper of [Guo et al.](#greedy2026) proves `2^{O(√(log log n))}` competitiveness; the stronger `O(log log n)` theorem stated here is a repository result.

### Cha-Cha

The source is [Čech et al., *Dynamic Optimality to within O(log log log n)*](#chacha2026). The algorithm is called **Cha-Cha**; its Lean namespace is `ChaCha`.

[`ChaChaAll.lean`](ChaChaAll.lean) exports one fixed deterministic online BST strategy for each finite key universe. It starts from any supplied tree, keeps exactly the original keys, and performs actual searches and ordinary rotations. Initialization is charged once. The final competitive theorem includes the construction and the lower-bound proof, with no remaining implementation or lower-bound assumption.

The [illustrated proof guide](docs/chacha-proof-guide/guide.pdf) connects the paper argument to Lean. The [repair notes](chacha/lean/PROOF_REPAIRS_2026_10_30.md) explain corrections and differences from the imported manuscript.

The same bound also holds for **Cha-Cha with ordinary Splay auxiliary trees**. Its [complete theorem](chacha/lean/ChaCha/Paper20261030/SplayAuxiliaryAll.lean) retains the persistent component shapes and ordinary Splay operations. For arbitrary universe sizes, the ordinary-Splay certificate applies to padded auxiliary bookkeeping, whose rotations are projected onto the original physical keys; it does not identify every pruned component operation with literal Splay. This variant uses Cha-Cha's two-level schedule. Classical MultiSplay has the separate theorem below.

### Classical MultiSplay

The formalization follows [Wang, Derryberry, and Sleator's algorithm](#multisplay2006), including the classical bottom-up switch order and final switch. The bound is

```text
cost(initial, X) = O((OPT(X) + n) · L₃(n) · g(ceil(log₂(n+1)))).
```

The composition applies the Splay analysis to components of logarithmic size and pays an additional `L₃(n)` for the comparison construction. The comparison algorithm and its physical implementation are both proved. The [proof guide](multisplay/COMPOSED_BOUND.txt) explains how the persistent forest of Splay components and the Cha-Cha comparison fit together; the [final Lean module](multisplay/lean/MultiSplay/CompetitiveLogHeight.lean) exports the result.

There is also a generic version, `competitive_generic_logarithmic`, for a monotone factor satisfying **`AdmissibleForestFactor`**: the factor must uniformly control the proved persistent Splay interface for searches, splits, and joins. Search competitiveness alone does not supply this stronger interface. The concrete factor `g` has a [proved admissibility instance](multisplay/lean/MultiSplay/GlobalPreferredGenericBound.lean).

## Further bounds and structural results

These results are part of the same checked library and use the same keys, request sequences, and optimum.

### Separating lower-bound counters

The Cha-Cha lower-bound proof uses alternations in fixed reference trees: changes between their left and right sides. Let `P` count primary-reference alternations, `D` count depth-reference fragment alternations, and `R` be the robust rectangle counter used in the proof. Their precise definitions and an explicit repeated bit-reversal family are given in the [separation guide](docs/separation-formalization-notes.txt).

On that family, with sequence length `m` and `F₀ = m + P + D`, the [separation theorem](chacha/lean/ChaCha/Separation/Explicit.lean) proves

```text
m ≤ F₀ ≤ 4m,
L₃(n) · F₀ ≤ 8R,       R ≤ 4 · L₃(n) · F₀.
```

Thus the robust counter can exceed the original length-plus-alternation counter by a factor `Θ(L₃(n))`, on the same request sequence and original key universe.

### An entropy-sensitive lower bound

An additional reference tree strengthens the original alternation counter: at each request time, take the larger of its event count and the original primary-plus-depth event count, then add the sequence length. The resulting counter `F_res` satisfies

```text
F_res(X) ≤ 519 · OPT(X)
```

for every ordering. Given key frequencies `pₓ`, one additional reference chosen from those frequencies, before the order is known, also satisfies

```text
E[F_res(X)] ≥ m · (1 + H) / (2 · log₂(3)),
where H = −Σₓ pₓ log₂(pₓ).
```

Here `H` is frequency entropy in bits, with zero-frequency terms contributing zero. The expectation is over uniformly random words with the given frequencies. The [entropy guide](docs/entropy-residual.txt) describes the constructed distribution and reference tree, and distinguishes this expectation bound from the deterministic comparison to `OPT`.

### Interleaved walks on ordered subsets

Suppose `k` sources each walk on a fixed ordered subset, staying at the current key or moving to its predecessor or successor in that subset. The subsets may overlap and their requests may be interleaved arbitrarily. For `m` total requests and `λ(k) = 1 + floor(log₂(k+1))`, [`Results.colored_shuffle`](DynamicOptimalityResults.lean) proves

```text
OPT(X) ≤ 292864 · m · λ(k)².
```

This is an offline optimum bound with no additive universe-size term. The proof constructs a static reference BST with several persistent search pointers, simulates it using ordinary rotations, and projects colored copies back to the original keys. From any supplied initial tree, an actual execution costs at most twice the displayed bound plus `12n`. The [walks and simulation guide](docs/colored-walks.txt) explains both logarithms and the connection to [multiple-finger BSTs](#multifinger2018).

### Funnel bounds under shuffling and decomposition

The **funnel count** `F(X)` counts side alternations among earlier occurrences visible from each request through empty closed rectangles. Repeated requests remain distinct occurrences. For every order-preserving interleaving `W` of two words `X` and `Y`, the [shuffle theorem](DynamicOptimality/Funnel/ShuffleOPT.lean) gives

```text
F(W) + |W| ≤ 360639 · (OPT(X) + OPT(Y)).
```

The source key sets may overlap, and there is no additive universe-size term. If the keys are partitioned into consecutive intervals, let `template` replace each request by its interval label and `partᵢ` retain the requests in interval `i`. The [composition theorem](DynamicOptimality/Funnel/ConvexComposition.lean) gives

```text
F(W) ≤ F(template) + Σᵢ F(partᵢ) + 9|W|.
```

The library also formalizes [Levy and Tarjan's approximate monotonicity argument](#levytarjan2022): deleting occurrences gives `F(subsequence) ≤ 4F(sequence) + 8|sequence|`.

### Structural tools and counterexamples

- **Reference-tree closure.** Adding the nearest common ancestors of each row's keys, in any fixed reference BST, preserves the geometric rectangle condition. A nonempty row of `r` keys grows to at most `2r−1` keys, and the union of rows in every closed time interval is also closed under nearest common ancestors. See the [closure guide](docs/reference-closure.txt) and [Lean statements](DynamicOptimality/ReferenceClosure.lean).
- **A logarithmic-height comparison execution.** An actual execution of cost `O(OPT+n)` has height `O(log(n+1))` at every intermediate state, rotations at depth at most one, and minor ribs of length at most 20. A minor rib follows one edge and then only edges in the opposite direction, ending at the adjacent null position. See [`LogHeightNormalForm`](splay/formalization/Splay/Accounting/LogHeightNormalForm.lean).
- **Limits of two MultiSplay proof approaches.** Ordinary Splay does not commute with restricting the key interval. A second, unbounded family refutes a specified per-request inequality using the classical sum-of-logarithms potential, even after adding any function of the primary preferred forest. These are counterexamples to those proof steps on legal supplied states; they assert no competitive lower bound. See the [precise statements](docs/multisplay-obstructions.txt).

## Model and scope

The library concerns **successful searches on a fixed finite ordered key set**. Navigation, computation, and mathematical bookkeeping are free in the search-and-rotation model. Cha-Cha and MultiSplay use fixed classical choices depending only on the current state and request. Their physical trees, rotations, costs, and consistency across prefixes are proved; an executable evaluator or bounded local controller is outside these statements.

As supporting results, [`BSTModels.lean`](DynamicOptimality/BSTModels.lean) relates five standard cost conventions:

| Model | Charged operations |
| --- | --- |
| **Root serving** | Bring the requested key to the root; charge requests and rotations. |
| **Search and rotations** | Charge the initial search depth plus one, then rotations. |
| **Single pointer** | Start at the root; charge adjacent moves, local rotations, and request service. |
| **Rooted subtree** | Rearrange a connected subtree containing the root and requested key; charge its size. |
| **Geometry** | Charge points in an arborally satisfied set of touches. |

A geometric point records a key and time. **Arboral satisfaction** means that every rectangle spanned by two points with different keys and times contains a third point, including its boundary. The formulation follows [Demaine et al.](#geometry2009) and assumes no BST realization.

For **all 25 ordered pairs** of models, a finite execution transfers with cost at most **481 times** its original cost. Initial trees may be freely chosen. Rooted-subtree and geometric executions have exactly the same attainable costs.

Online conversions are proved as well, including both directions between trees and geometry. From the standard free geometric baseline, [`Results.geometric_online`](DynamicOptimalityResults.lean) constructs one physical BST strategy before future requests, with

```text
BST cost ≤ 381 · geometric cost + 387n
```

for every prefix and every supplied initial BST. The additive term pays initialization once. See the [five-model guide](docs/BST_MODELS.txt) and the [online simulation construction](docs/geometric-online-simulation.txt).

## Explore the proofs

The [interactive proof graph](https://vaclavrozhon.github.io/dynamic-optimality/proof-atlas.html) displays modules or individual declarations, with an edge for a direct dependency. Main results are starred and have navigation buttons. Use the wheel or buttons to zoom; hover over a vertex to highlight its incident edges. The current graph contains **69,472 declarations, including 43,646 theorems**.

| To find… | Start here |
| --- | --- |
| The main competitive statements | [Public entry point](DynamicOptimalityResults.lean) |
| Definitions, assumptions, and proof dependencies | [Formalization map](FORMALIZATION.md) |
| Splay's analysis | [Splay proof map](splay/formalization/COMPLETED_PROOF.md) |
| Cha-Cha's paper-to-Lean argument | [PDF proof guide](docs/chacha-proof-guide/guide.pdf) |
| The MultiSplay composition | [Composed-bound guide](multisplay/COMPOSED_BOUND.txt) |
| A shareable overview | [Project website](https://vaclavrozhon.github.io/dynamic-optimality/) |

The graph also works [offline as a standalone HTML file](https://github.com/vaclavrozhon/dynamic-optimality/raw/refs/heads/main/docs/dependency-graph.html). Its [guide](docs/DEPENDENCY_GRAPH.md) explains the controls and how to rebuild it. `make guide` rebuilds the Cha-Cha PDF using pdfLaTeX and standard TeX packages, including TikZ.

## Build and check the proofs

Install [elan](https://github.com/leanprover/elan), clone this repository, and run:

```sh
git clone https://github.com/vaclavrozhon/dynamic-optimality.git
cd dynamic-optimality
elan toolchain install leanprover/lean4:v4.32.1
lake exe cache get
make audit
```

The [Lean toolchain](lean-toolchain) and [dependency manifest](lake-manifest.json) are pinned. The first dependency and cache retrieval requires network access. The full build can require substantial memory; run builds and audits one at a time.

`make audit` builds **every registered Lean module** and checks the logical dependencies of **every local declaration**, including private and generated declarations. It also checks the public endpoints in [AuditAll.lean](AuditAll.lean) and [AuditDynamicOptimality.lean](AuditDynamicOptimality.lean). The only accepted axioms are `propext`, `Classical.choice`, and `Quot.sound`; proof gaps such as `sorry` fail the audit. The [audit runner](tools/audit.py) checks module coverage as part of the process.

**Verified on 2 November 2026:** all **2,507 modules** built, **69,472 declarations** passed the axiom audit, and **406 explicit endpoint diagnostics** passed. The corresponding [GitHub Actions run](https://github.com/vaclavrozhon/dynamic-optimality/actions/runs/41469561886) also passed. The [verification record](docs/verification-additional-2026-11-02.txt) and [source hashes](docs/snapshots/2026-11-02.additional.sources.sha256) identify the checked snapshot. The [semantic review](docs/additional-review-2026-11-02.txt) records the scope checks; the axiom audit alone does not assess whether a definition captures the intended mathematics.

[GitHub Actions](https://github.com/vaclavrozhon/dynamic-optimality/actions/workflows/lean.yml) repeats the full build and audit on subsequent pushes.

## Citing the formalization

Use [`CITATION.bib`](CITATION.bib) to cite the verified source snapshot. Its link names an immutable commit, so readers can recover the exact artifact. Use the [project website](https://vaclavrozhon.github.io/dynamic-optimality/) for the evolving overview and proof graph. Bibliographic entries for the papers below are available in [`docs/references.bib`](docs/references.bib).

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

This repository began with a source snapshot of the shared workspace on 1 November 2026 and includes substantial later work. The original [Splay Git history](https://github.com/vaclavrozhon/splay) remains separate. See the [provenance record](docs/PROVENANCE.txt) for the imported sources and the [latest verified source hashes](docs/snapshots/2026-11-02.additional.sources.sha256) for the current proof snapshot.

No license has yet been selected for this repository. Dependency licenses do not determine the license of these sources.

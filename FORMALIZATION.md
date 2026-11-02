# Formalization map

This document describes the current exported statements and their remaining boundaries. The repository contains the registered Lean developments and three additional root audit files. The source snapshot preserves their relative paths so the shared Lake configuration can resolve every local import. Experimental programs, datasets, dependency caches, and archived literature are not build inputs.

The [2 November library review](docs/review-2026-11-02.txt) records the generic MultiSplay refactor and broader audit coverage. The [verification record](docs/verification-review-2026-11-02.txt) covers every current registered module and declaration; the older records below describe their respective milestones.

## Shared trees, optimum, and online strategies

[DynamicOptimality.Basic](DynamicOptimality/Basic.lean) reuses two existing tree types. `BST lower upper` stores exactly the natural keys in the interval `[lower, upper)`, with ordering enforced by its type. `RawTree` stores the same ordinary binary-tree structure without interval indices. `BST.toRaw` preserves its keys, children, and ordering.

[DynamicOptimality.Cost](DynamicOptimality/Cost.lean) reuses the attained offline optimum from the splay development. `OPT requests` minimizes one unit per request plus the number of ordinary rotations in executions that bring each requested key to the root. The initial tree is freely chosen by the optimum. `Competitive cost factor` quantifies one positive constant uniformly over all nonempty universes, all supplied initial indexed trees, and all finite request words, with bound `C * (OPT requests + n) * factor n`.

[SearchRotationModel](DynamicOptimality/SearchRotationModel.lean) defines the Cha-Cha cost model. An access first searches its current tree, paying depth plus one, and then performs a finite sequence of ordinary rotations, paying one per rotation. Rotations may occur at any subtree; navigation and other computation are free. An execution continues from the exact preceding output tree. [SearchRotationEquivalence](DynamicOptimality/SearchRotationEquivalence.lean) compares this model with the same shared `OPT` within a factor of two in either direction.

[OnlineBST](DynamicOptimality/OnlineBST.lean) packages a state, its one actual tree, a successor function, and an access cost. Its legality field certifies an actual search-and-rotation access between those trees. The successor and cost depend only on the current state and request. `run_append` establishes exact prefix consistency. The state may contain arbitrary mathematical bookkeeping; classical choice is allowed, and effectiveness of evaluation is not asserted.

## Equivalent BST models

[BSTModels](DynamicOptimality/BSTModels.lean) compares five models on the same original keys: root service charged by requests plus rotations; initial search depth plus one followed by rotations; an adjacent pointer charged for moves, local rotations, and service; replacement of a connected root-containing part of the tree, charged by its number of nodes; and geometric touches. The connected replacement preserves every untouched hanging subtree. In geometry, a point `(key,time)` records a touched key. A point set is *arborally satisfied* when every closed axis-aligned rectangle determined by two points in different rows and columns contains a third point, possibly on its boundary. [GeometricModel](DynamicOptimality/GeometricModel.lean), particularly `Geometry.execution_iff_points`, proves that this ordinary point condition defines the geometric model without an assumed BST realization.

`BSTModel.transfer` converts finite executions between every ordered pair of models. `BSTModel.all_five_equivalent` gives one common factor of 481, uniformly over all universes and request sequences, including empty cases. Initial trees are freely chosen and reconstruction may depend on the complete sequence. The more precise comparison factors and definitions are in [ModelCostEquivalence](DynamicOptimality/ModelCostEquivalence.lean) and [GeometricCost](DynamicOptimality/GeometricCost.lean). The latter's `ModelCosts.geometry_iff_hull` proves exact equality of attainable hull and geometric costs; its reverse uses the backwards reconstruction in [GeometricToBST](DynamicOptimality/GeometricToBST.lean). `BSTModel.competitive_iff` permits any of the five models for the competitor while retaining the existing algorithm cost and shared `OPT`.

[ModelInitialization](DynamicOptimality/ModelInitialization.lean) supplies executions from any prescribed initial BST, with costs at most `OPT+6n`, `2*OPT+12n`, `OPT+6n`, and `37*OPT+222n` in the root, search, hull, and pointer models respectively. Here `n` is the number of keys. The startup allowance is paid once, the first search is charged in the supplied tree, and the empty word performs no setup.

There are also online conversions between the four tree models in [ModelOnline](DynamicOptimality/ModelOnline.lean) and [ModelOnlineNormalization](DynamicOptimality/ModelOnlineNormalization.lean). An arbitrary `OnlineBST` is simulated by root, hull, and pointer strategies with factors 2, 2, and 74 on every finite prefix, preserving its initial physical tree. The simulator may postpone remote rotations and have a different later physical tree, related to the source by an explicit pending rotation sequence. [GeometricOnline](DynamicOptimality/GeometricOnline.lean) gives a pure online geometric interface, an exact-cost hull-to-geometry conversion, and a factor-two search-to-geometry conversion. [GeometricOnlineGreedy](DynamicOptimality/GeometricOnlineGreedy.lean) places the actual existing Greedy algorithm in that interface with unchanged rows and cost.

The arbitrary **online geometry-to-BST conversion is deferred**. The finite backwards reconstruction does not establish it, and the current results do not export a physical online Greedy BST. See [the model guide](docs/BST_MODELS.txt) for exact constants, theorem names, and the distinction between finite cost equivalence and online simulation.

The full build and both namespace audits passed with these modules imported on 1 November 2026. The [verification record](docs/verification-bst-models.txt) records the commands, declaration counts, and public endpoints.

## Exported results

[DynamicOptimalityResults.lean](DynamicOptimalityResults.lean) is the short common entry point. The factor notation below uses `Lₖ(n) = Splay.Analysis.iteratedLog k n`: start with `n`, then apply `ceil(log₂(max(2, ·)))` exactly `k` times.

| Result | Statement and scope |
| --- | --- |
| `DynamicOptimality.Results.splay` | `Competitive Splay.Accounting.concreteSplayCost Splay.Analysis.targetFactor`, where the factor is `L₂(n) * L₃(n)^2`. |
| `DynamicOptimality.Results.splay_refined` | The same actual splay cost with the additional proved factor `Splay.Analysis.egTargetFactor`; its exact definition is in [IteratedLogEGBound](splay/formalization/Splay/Accounting/IteratedLogEGBound.lean). The original `DynamicOptimality.splay_eg_competitive` name remains available. |
| `DynamicOptimality.Results.greedy` | `Competitive Greedy.cost Greedy.loglogFactor`, where `loglogFactor = L₂`. |
| `DynamicOptimality.Results.chacha` | `Competitive DynamicOptimality.ChaCha.All.cost (Splay.Analysis.iteratedLog 3)`. |
| `DynamicOptimality.Results.multisplay` | `Competitive MultiSplay.Online.cost (MultiSplay.logarithmicFactor Splay.Analysis.egTargetFactor)`, with factor `L₃(n) * egTargetFactor (ceil(log₂(n+1)))`. |

Splay's cost counts requests and its actual standard rotations. Greedy's cost counts geometric touches from the surface determined by the supplied initial BST; a geometric point represents a key touched at a request time. These cost conventions remain explicit. The Greedy theorem does not itself export a strategy through `OnlineBST`.

The detailed splay and Greedy proof maps are [COMPLETED_PROOF.md](splay/formalization/COMPLETED_PROOF.md) and [README.txt](greedy/formalization/README.txt). The shared files [SplayBound](DynamicOptimality/SplayBound.lean) and [SplayBlackBoxBound](DynamicOptimality/SplayBlackBoxBound.lean) export existing results with the common optimum rather than introducing another one.

## Cha-Cha: actual online BST accesses on every universe

The final interface is [ChaChaAll.lean](ChaChaAll.lean), in namespace `DynamicOptimality.ChaCha.All`:

- `strategy` is an `OnlineBST n`; its tree contains exactly `0,...,n-1`.
- `initial_tree` identifies its initial physical tree with any supplied `BST 0 n`.
- `execution` certifies the actual searches and rotations at the reported cost.
- `online` preserves the exact state and accumulated cost of every prefix.
- `empty_word` and `zero_universe` cover the empty cases.
- `third_log_competitive` proves the unrestricted shared competitive statement.

The proof has four connected stages.

1. Persistent primary and secondary preference histories are charged to a robust rectangle count, a geometric lower-bound quantity defined from the actual requests. The count is bounded by the shared BST optimum. The maintained component construction produces actual metadata-decorated BST accesses. [OnlineSharedOPT](chacha/lean/ChaCha/Paper20261030/OnlineSharedOPT.lean) bounds one fixed online sequence of these accesses.
2. [SearchRotationMetadata](chacha/lean/ChaCha/Paper20261030/SearchRotationMetadata.lean) erases metadata while preserving real keys and both tree endpoints. It bounds the requested key's depth in the original tree, even when the source trace rotates before serving it. The resulting search-and-rotation cost is at most twice the source metadata cost. [OnlineSearchRotation](chacha/lean/ChaCha/Paper20261030/OnlineSearchRotation.lean) fixes this conversion separately for each current state and request.
3. [OnlineSearchRotationInitialization](chacha/lean/ChaCha/Paper20261030/OnlineSearchRotationInitialization.lean) accepts any initial tree. The first request searches that supplied tree before initialization rotations. A permanent transition from fresh to active state charges initialization only once. [ChaChaAbstract.lean](ChaChaAbstract.lean) exports the power-of-two construction through `OnlineBST`.
4. [UniverseExtension](DynamicOptimality/UniverseExtension.lean) embeds an arbitrary universe into a power-of-two virtual universe. [SearchRotationProjection](DynamicOptimality/SearchRotationProjection.lean) removes every virtual key from the physical tree: each source rotation induces at most one physical rotation, and initial search depth cannot increase. [OnlineBSTProjection](DynamicOptimality/OnlineBSTProjection.lean) fixes those projected transitions online. Pruning the extended initial tree returns the exact supplied original tree. The extra keys exist only in free internal bookkeeping.

[PaddingSize](DynamicOptimality/PaddingSize.lean) bounds the virtual universe by `4n` for `n > 0`; `UniverseExtension.OPT_castLE_le` bounds its embedded optimum by `6 * OPT`. [PaddingFactor](DynamicOptimality/PaddingFactor.lean) bounds the resulting factor by `4 * L₃(n)`. The explicit final theorem is

```text
cost initial requests
  ≤ 3237120000456 * (OPT requests + n) * L₃(n).
```

The [proof guide](docs/chacha-proof-guide/guide.pdf) explains the mathematical argument. [PROOF_REPAIRS_2026_10_30.md](chacha/lean/PROOF_REPAIRS_2026_10_30.md) records corrections and implementation differences from the imported manuscript. The stronger bounded local-controller model is separate from the completed abstract theorem; historical controller modules remain available without becoming additional hypotheses of the final result.

## Classical MultiSplay: the composed bound

[MultiSplay.CompetitiveLogHeight](multisplay/lean/MultiSplay/CompetitiveLogHeight.lean) proves the composed bound for the classical algorithm. Its factor is `L₃(n) * g(ceil(log₂(n+1)))`, where `g = Splay.Analysis.egTargetFactor` is the strongest existing exported Splay factor. The common entry point is `DynamicOptimality.Results.multisplay`. [MultiSplayBound](DynamicOptimality/MultiSplayBound.lean) exports this precise version as `multisplay_logarithmic_competitive` and retains the convenient `L₃(n) * g(2L₁(n))` version as `multisplay_competitive`.

[InitializedOnline](multisplay/lean/MultiSplay/InitializedOnline.lean) defines one fixed online strategy on exactly the original keys. Its `execution`, `online`, `initial_tree`, and `exact_keys` statements certify ordinary searches and rotations, prefix consistency, and the supplied initial tree. The classical bottom-up switch schedule, including the final switch, is retained. Initialization contributes at most one `19*n` allowance. [InitializedClassicalExecution](multisplay/lean/MultiSplay/InitializedClassicalExecution.lean) certifies the exact initial rotation transcript and the retained classical chronology. The empty word and empty universe are covered.

The argument has four stages, explained in [COMPOSED_BOUND.txt](multisplay/COMPOSED_BOUND.txt).

1. [GlobalPreferredInventoryHistory](multisplay/lean/MultiSplay/GlobalPreferredInventoryHistory.lean) replays the exact chosen physical run as a persistent forest of splay components. [GlobalPreferredForestBound](multisplay/lean/MultiSplay/GlobalPreferredForestBound.lean) applies the common-forest Splay comparison to that same run, at reference height `H = (balancedReference n).height`. All component domains, capacity checks, distinctness, and initialization charges are proved. The resulting cost is `O((n+Q)*g(H) + |X|)`, where `Q` is a comparator budget for the literal chronological event word.
2. [ComparatorStableTransaction](multisplay/lean/MultiSplay/ComparatorStableTransaction.lean) maintains secondary source trees on reference depths and performs the stable prefix/tail exchange with persistent row memory. [ComparatorGuardStableService](multisplay/lean/MultiSplay/ComparatorGuardStableService.lean) projects these operations onto ordinary original-key trees and executes the exact guard searches, splits, and joins in both directions. Guard identities follow from the actual preferred path, including absent guards and empty children.
3. [ComparatorConcreteService](multisplay/lean/MultiSplay/ComparatorConcreteService.lean) supplies the concrete selected-pair service. [ComparatorForestService](multisplay/lean/MultiSplay/ComparatorForestService.lean) frames unchanged components and preserves the global representation and memory. [ComparatorProgramChronology](multisplay/lean/MultiSplay/ComparatorProgramChronology.lean) composes these services without resetting component shapes or row bits. The comparator costs `O(comparisonFactor H * (S+V))`, where `S` counts actual classical switches and `V` is persistent secondary-ledger variation.
4. [BalancedReference](multisplay/lean/MultiSplay/BalancedReference.lean) bounds `|X|+S+V` by `2137120*(OPT X+n)` on an exactly `n`-key balanced reference. [ComparatorCompetitiveReduction](multisplay/lean/MultiSplay/ComparatorCompetitiveReduction.lean) and [InitializedComparatorBound](multisplay/lean/MultiSplay/InitializedComparatorBound.lean) combine the charges. [CompetitiveEGFactor](multisplay/lean/MultiSplay/CompetitiveEGFactor.lean) translates `comparisonFactor H * g(H)` to the stated logarithmic factor. The final `Online.competitive` theorem has no comparator, simulation, or representation-invariant premise.

`Online.composed_bound` gives the exact-height bound, uniformly also for an empty universe. `Online.competitive_expanded` gives the explicit factor `L₃(n)^2 * L₄(n) * E(48*L₃(n))`, where `E` is the coefficient envelope from [LayerEnvelope](splay/formalization/Splay/Analysis/LayerEnvelope.lean). This is the composition with one extra outer `L₃`; it does not assert the stronger bound without that factor.

The generalization is `Online.competitive_generic`: any `g : Nat → Nat` with `AdmissibleForestFactor g` yields factor `comparisonFactor H * g(H)`. Admissibility means that `g` uniformly dominates the factor supplied by some proved persistent Splay interface coefficients at the constructed normalizer cap. It introduces no comparator assumption. With monotone `g`, `Online.competitive_generic_logarithmic` yields the sharper `L₃(n)*g(ceil(log₂(n+1)))`; `Online.competitive_generic_shifted` also gives `L₃(n)*g(2L₁(n))`. This is a generalization through the split/join interface; an arbitrary query-only Splay competitiveness theorem is not silently substituted for that interface. Replacing `g(2t)` by `O(g(t))` requires an additional scaling property, even when `g` is monotone; the formal theorem retains the factor two in its argument.

The concrete factor's admissibility is proved by `admissible_egTargetFactor` in [GlobalPreferredGenericBound](multisplay/lean/MultiSplay/GlobalPreferredGenericBound.lean), with a fixed coefficient function and domination constant `16*168`. The concrete forest, initialization, and logarithmic-capacity bounds now specialize the generic arguments. [ComparatorEstimate](multisplay/lean/MultiSplay/ComparatorEstimate.lean) contains the shared exact-word comparator premise; `Online.comparator_estimate` discharges it using the actual comparator construction.

The complete build and both namespace axiom audits passed on 1 November 2026; see the [verification record](multisplay/verification.txt).

The earlier [composition audit](multisplay/composition-audit.tex), [forest normal form](multisplay/common-forest-normal-form.tex), and [comparator draft](multisplay/chacha-common-forest-comparator.tex) remain research documents. Their warnings about missing bridges describe earlier stages; the definitive current statements are the Lean endpoints and this map.

## Verification and repository boundaries

Use the pinned root [Lake configuration](lakefile.toml), [manifest](lake-manifest.json), and [toolchain](lean-toolchain). Several required sources retain research-directory paths under `interface/`, `splay/research/`, and `greedy/`; they are ordinary registered Lean modules, not optional data files.

Run `make audit` before reporting a complete verified change. The [runner](tools/audit.py) builds every registered module, imports a compiler-derived frontier covering the full inventory, runs both root audit files' explicit endpoint diagnostics, and audits all declarations by their originating module. This covers local declarations outside the historical namespace filters and modules outside the public entry points' import closure. The original [AuditAll.lean](AuditAll.lean), [AuditDynamicOptimality.lean](AuditDynamicOptimality.lean), and [AuditGreedy.lean](AuditGreedy.lean) remain available as narrower direct checks. The allowed logical axioms are `propext`, `Classical.choice`, and `Quot.sound`. Auditing these dependencies complements, rather than replaces, review of definitions and theorem hypotheses.

The [snapshot hashes](docs/snapshots/2026-11-02.review.sources.sha256) record the reviewed sources, not a fresh build certificate for another machine. Record build and audit outcomes separately when reproducing them. [PROVENANCE.txt](docs/PROVENANCE.txt) explains the preserved splay history and omitted workspace material. No repository license has yet been selected.

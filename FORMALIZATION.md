# Formalization map

This document describes the current exported statements and their remaining boundaries. The repository contains 2085 registered Lean modules and three additional root audit files. The source snapshot preserves their relative paths so the shared Lake configuration can resolve every local import. Experimental programs, datasets, dependency caches, and archived literature are not build inputs.

## Shared trees, optimum, and online strategies

[DynamicOptimality.Basic](DynamicOptimality/Basic.lean) reuses two existing tree types. `BST lower upper` stores exactly the natural keys in the interval `[lower, upper)`, with ordering enforced by its type. `RawTree` stores the same ordinary binary-tree structure without interval indices. `BST.toRaw` preserves its keys, children, and ordering.

[DynamicOptimality.Cost](DynamicOptimality/Cost.lean) reuses the attained offline optimum from the splay development. `OPT requests` minimizes one unit per request plus the number of ordinary rotations in executions that bring each requested key to the root. The initial tree is freely chosen by the optimum. `Competitive cost factor` quantifies one positive constant uniformly over all nonempty universes, all supplied initial indexed trees, and all finite request words, with bound `C * (OPT requests + n) * factor n`.

[SearchRotationModel](DynamicOptimality/SearchRotationModel.lean) defines the Tango² cost model. An access first searches its current tree, paying depth plus one, and then performs a finite sequence of ordinary rotations, paying one per rotation. Rotations may occur at any subtree; navigation and other computation are free. An execution continues from the exact preceding output tree. [SearchRotationEquivalence](DynamicOptimality/SearchRotationEquivalence.lean) compares this model with the same shared `OPT` within a factor of two in either direction.

[OnlineBST](DynamicOptimality/OnlineBST.lean) packages a state, its one actual tree, a successor function, and an access cost. Its legality field certifies an actual search-and-rotation access between those trees. The successor and cost depend only on the current state and request. `run_append` establishes exact prefix consistency. The state may contain arbitrary mathematical bookkeeping; classical choice is allowed, and effectiveness of evaluation is not asserted.

## Exported results

[DynamicOptimalityResults.lean](DynamicOptimalityResults.lean) is the short common entry point. The factor notation below uses `Lₖ(n) = Splay.Analysis.iteratedLog k n`: start with `n`, then apply `ceil(log₂(max(2, ·)))` exactly `k` times.

| Result | Statement and scope |
| --- | --- |
| `DynamicOptimality.Results.splay` | `Competitive Splay.Accounting.concreteSplayCost Splay.Analysis.targetFactor`, where the factor is `L₂(n) * L₃(n)^2`. |
| `DynamicOptimality.splay_eg_competitive` | The same actual splay cost with the additional proved factor `Splay.Analysis.egTargetFactor`; its exact definition is in [IteratedLogEGBound](splay/formalization/Splay/Accounting/IteratedLogEGBound.lean). |
| `DynamicOptimality.Results.greedy` | `Competitive Greedy.cost Greedy.loglogFactor`, where `loglogFactor = L₂`. |
| `DynamicOptimality.Results.tango2` | `Competitive DynamicOptimality.Tango2.All.cost (Splay.Analysis.iteratedLog 3)`. |

Splay's cost counts requests and its actual standard rotations. Greedy's cost counts geometric touches from the surface determined by the supplied initial BST; a geometric point represents a key touched at a request time. These cost conventions remain explicit. The Greedy theorem does not itself export a strategy through `OnlineBST`.

The detailed splay and Greedy proof maps are [COMPLETED_PROOF.md](splay/formalization/COMPLETED_PROOF.md) and [README.txt](greedy/formalization/README.txt). The shared files [SplayBound](DynamicOptimality/SplayBound.lean) and [SplayBlackBoxBound](DynamicOptimality/SplayBlackBoxBound.lean) export existing results with the common optimum rather than introducing another one.

## Tango²: actual online BST accesses on every universe

The final interface is [TangoSquaredAll.lean](TangoSquaredAll.lean), in namespace `DynamicOptimality.Tango2.All`:

- `strategy` is an `OnlineBST n`; its tree contains exactly `0,...,n-1`.
- `initial_tree` identifies its initial physical tree with any supplied `BST 0 n`.
- `execution` certifies the actual searches and rotations at the reported cost.
- `online` preserves the exact state and accumulated cost of every prefix.
- `empty_word` and `zero_universe` cover the empty cases.
- `third_log_competitive` proves the unrestricted shared competitive statement.

The proof has four connected stages.

1. Persistent primary and secondary preference histories are charged to a robust rectangle count, a geometric lower-bound quantity defined from the actual requests. The count is bounded by the shared BST optimum. The maintained component construction produces actual metadata-decorated BST accesses. [OnlineSharedOPT](tango_squared/lean/TangoSquared/Paper20261030/OnlineSharedOPT.lean) bounds one fixed online sequence of these accesses.
2. [SearchRotationMetadata](tango_squared/lean/TangoSquared/Paper20261030/SearchRotationMetadata.lean) erases metadata while preserving real keys and both tree endpoints. It bounds the requested key's depth in the original tree, even when the source trace rotates before serving it. The resulting search-and-rotation cost is at most twice the source metadata cost. [OnlineSearchRotation](tango_squared/lean/TangoSquared/Paper20261030/OnlineSearchRotation.lean) fixes this conversion separately for each current state and request.
3. [OnlineSearchRotationInitialization](tango_squared/lean/TangoSquared/Paper20261030/OnlineSearchRotationInitialization.lean) accepts any initial tree. The first request searches that supplied tree before initialization rotations. A permanent transition from fresh to active state charges initialization only once. [TangoSquaredAbstract.lean](TangoSquaredAbstract.lean) exports the power-of-two construction through `OnlineBST`.
4. [UniverseExtension](DynamicOptimality/UniverseExtension.lean) embeds an arbitrary universe into a power-of-two virtual universe. [SearchRotationProjection](DynamicOptimality/SearchRotationProjection.lean) removes every virtual key from the physical tree: each source rotation induces at most one physical rotation, and initial search depth cannot increase. [OnlineBSTProjection](DynamicOptimality/OnlineBSTProjection.lean) fixes those projected transitions online. Pruning the extended initial tree returns the exact supplied original tree. The extra keys exist only in free internal bookkeeping.

[PaddingSize](DynamicOptimality/PaddingSize.lean) bounds the virtual universe by `4n` for `n > 0`; `UniverseExtension.OPT_castLE_le` bounds its embedded optimum by `6 * OPT`. [PaddingFactor](DynamicOptimality/PaddingFactor.lean) bounds the resulting factor by `4 * L₃(n)`. The explicit final theorem is

```text
cost initial requests
  ≤ 3237120000456 * (OPT requests + n) * L₃(n).
```

The [proof guide](docs/tango2-proof-guide/guide.pdf) explains the mathematical argument. [PROOF_REPAIRS_2026_10_30.md](tango_squared/lean/PROOF_REPAIRS_2026_10_30.md) records corrections and implementation differences from the imported manuscript. The stronger bounded local-controller model is separate from the completed abstract theorem; historical controller modules remain available without becoming additional hypotheses of the final result.

## Classical MultiSplay: established interfaces and remaining work

The target is the unchanged classical MultiSplay algorithm. Its preferred-path switches run in a different order from the Tango² head loop, so serving the same original request word is not sufficient to transfer the upper bound.

[CommonForestSplayBound](multisplay/lean/MultiSplay/CommonForestSplayBound.lean) proves a comparison for a supplied actual splay execution of a fixed chronological word of searches, splits, and joins. Its comparator must execute that exact word on the prescribed component key domains. Distinctness is global across the live forest, and capacity and join-size conditions are explicit. The comparison retains history through component splits and joins, with one initialization allowance.

[EndpointCounterBound](multisplay/lean/MultiSplay/EndpointCounterBound.lean) bounds the actual chronological switch count and persistent secondary-ledger variation by the shared optimum. For a perfect reference with `n` keys, the bound is `2137120 * OPT requests + 21 * n`, including one unit per original request. This is a counter theorem, not a physical-cost upper bound.

The remaining work is to construct the inexpensive comparator for the exact classical forest word, and to bound the whole algorithm's physical search and rotation cost by its replay. Only after both bridges are proved should full MultiSplay competitiveness be exported. Start from the [composition audit](multisplay/composition-audit.tex), [forest normal form](multisplay/common-forest-normal-form.tex), and [comparator draft](multisplay/tango-common-forest-comparator.tex). The twelve LaTeX drafts are research documents, not substitutes for these missing Lean statements.

## Verification and repository boundaries

Use the pinned root [Lake configuration](lakefile.toml), [manifest](lake-manifest.json), and [toolchain](lean-toolchain). Several required sources retain research-directory paths under `interface/`, `splay/research/`, and `greedy/`; they are ordinary registered Lean modules, not optional data files.

Run `lake build`, then `make audit` before reporting a complete verified change. The latter also runs the build and invokes [AuditAll.lean](AuditAll.lean) and [AuditDynamicOptimality.lean](AuditDynamicOptimality.lean). [AuditGreedy.lean](AuditGreedy.lean) supplies an additional focused audit. The allowed logical axioms are `propext`, `Classical.choice`, and `Quot.sound`. Auditing these dependencies complements, rather than replaces, review of definitions and theorem hypotheses.

The [snapshot hashes](docs/snapshots/2026-11-01.sources.sha256) record the copied sources, not a fresh build certificate for another machine. Record build and audit outcomes separately when reproducing them. [PROVENANCE.txt](docs/PROVENANCE.txt) explains the preserved splay history and omitted workspace material. No repository license has yet been selected.

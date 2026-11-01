# Completed concrete splay theorem

The main result is `Splay.concreteTargetBound` in
[ConcreteTargetBound.lean](Splay/Accounting/ConcreteTargetBound.lean), imported
by `Splay.lean`. It has no theorem arguments:

```lean
theorem concreteTargetBound :
    TargetBound Accounting.OfflineOptimum.concreteOfflineCostModel
```

Unfolding this statement gives one constant `C > 0` such that, for every
`n > 0`, initial `BST 0 n`, and access sequence,

```text
concreteSplayCost initial accesses
  ≤ C * (offlineOptCost accesses + n) * targetFactor n.
```

The splay cost is the number of requests plus the exact number of ordinary
rotations in the chosen standard splay execution. The offline cost is an
attained minimum over actual root-serving BST rotation executions, not a free
cost parameter. `targetFactor n` is `iteratedLog 2 n * (iteratedLog 3 n)^2`,
where each logarithm is the base-two ceiling logarithm of `max 2 n`.

## Final dependency path

1. `OfflineConnectedNormalization` normalizes arbitrary offline rotations to
   connected request support with cost multiplier two. The restricted-path,
   folded-stack, heavy-representation, and rib-simulation constructions give
   actual comparison executions.
2. `ConstructedPolylogNormalForm` chooses one such comparison trace, with
   cost at most `400000000 * (offlineOptCost accesses + n)`, height at most
   `54000 * stabilizedLog n ^ 3`, rotation depth at most one, and relevant
   neighbor-depth slack at most twenty. Its stronger local structural data
   is retained by the actual schedule.
3. `ArticleCompleteRequest`, `ArticleComparisonExecution`, and
   `ArticleInitializedExecution` construct one actual chronological rich
   trace, including initialization, temporary priorities, both internal
   pairing passes, both boundary phases, transfers, priority restoration,
   and every comparison rotation. Event counts refer to this same trace.
4. `ArticleGlobalUnbroken` proves the passed-block invariant through that
   chronology. The proof includes junction changes, root-changing comparison
   rotations, off-path subtree persistence, and the first-splay final-spine
   geometry. No unbrokenness provider remains as an input.
5. `ArticlePreparedPairingFraction` proves the bound on the literal selected
   internal rows. `ArticleBoundaryPairCount` proves at most four actual
   boundary losers per admissible source during one request.
6. `BoundarySizeCredit`, `BoundaryBlockCredit`, and `BoundaryCreditEffects`
   prove the capped logarithmic potential inequalities for all interface
   operations. `ArticleSourceCredit` charges the actual first pass in each
   source macro. `BoundaryRelocationCredit`, `ArticleBoundaryPhaseCredit`,
   and `ArticlePairingBoundaryCredit` charge actual deletions from small
   sources and cover every other boundary loser by an executed work item.
7. `ArticlePairingBoundaryEstimate`, `ArticleMacroBoundaryCredit`, and
   `ArticleInitializedBoundaryEstimate` telescope those inequalities over
   the complete constructed run, using only its historical creation budget
   and its own actual activity.
8. `BoundaryCreditAbsorption`, `BoundaryCreditUniformBound`, and
   `ArticleUniformPairingBound` choose uniform constants before quantifying
   over tree sizes and sequences, then absorb the boundary term. Together
   with `ArticleGlobalBends` and the exact concrete splay transcript, this
   proves `ConstructedPolylogNormalForm.hasCoreAnalysisBound`.
9. `ConcreteTargetBound` applies the proved normal-form and polylogarithmic
   height-factor bridges to that unconditional core bound.

## The global credit calculation

For an arbitrary cutoff `κ`, put `K = clog 2 (κ^16 + 1)`. A growing block
reserves `K + 13` credit. A shrinking block of size `s` and pass count `p`
has credit

```text
min K (clog 2 (s^16 + 1)) + (if p = 0 then 1 else 0) + min 12 s.
```

Creating a block supplies its reserve; splitting is paid by the new physical
block IDs. Growing insertion and conversion respect the reserve. A first
pass spends the initial unit even if its matching is empty. An admissible
fractional pass with `0 < s ≤ κ` spends a logarithmic unit. A deletion from
a source of size at most twelve spends a unit of the final summand.

Let `A` be actual interface activity, `B` the number of boundary rows, and
`N = n + comparisonTrace.cost`. The completed concrete run satisfies, for
every `κ`,

```text
κ * (2 * B) ≤ 319420 * κ * (K + 13) * N + 16 * A.
```

The unconditional interface theorem gives a uniform coefficient `c > 0`
with `A ≤ c * G * (clog 2 G + 1) * (N + B)`. Choosing
`κ = 32 * c * G^2` makes the boundary term absorbable, while
`K + 13 ≤ (16 * clog 2 (32*c) + 46) * (clog 2 G + 1)`.
Thus `A + B` is bounded by a uniform multiple of
`N * G * (clog 2 G + 1)^2`. The doubled-priority value cap contributes at
most eighteen times the public `heightFactor`.

## Clarifications and repairs retained in the proof

- Polylogarithmic comparison height suffices for the requested final factor.
  The completed proof does not require the stronger logarithmic-height
  normal-form interface discussed in earlier notes.
- The actual scheduler uses two exempt passes and matching fraction one
  eighth. Sources with initial pass count zero are enumerated even when
  their two matchings are empty; their first-pass credit is therefore tied
  to a real operation.
- The inequality `unimportant ≤ paid` is not assumed. The actual global
  boundary estimate and the larger freely chosen cutoff supply absorption.
- Unbrokenness before a source's first splay is not presumed. The required
  first-splay geometry and subsequent preservation are proved.
- Earlier diagnostic counterexamples and conditional compatibility APIs
  remain available. They do not supply premises to the final theorem.

## Verification

Final verification on 2026-09-11 passed: `lake build` completed 3,489 jobs;
the audit checked 19,571 project declarations with no nonstandard axioms.
Its import closure covers all 491 project Lean modules. The explicitly
expanded concrete theorem also elaborated successfully. `git diff --check`
and the source scan for proof placeholders passed.

Use the pinned Lean and Mathlib `v4.32.1`, and run these commands sequentially
from this directory:

```sh
lake build
lake env lean review/Review20260910.lean
```

The audit checks an explicitly expanded version of the concrete final
statement, prints the final theorem's axioms, and checks every `Splay` and
private `Splay` declaration, including generated declarations. Only
`propext`, `Classical.choice`, and `Quot.sound` are allowed. There are no
`sorry`, `admit`, custom axioms, or `native_decide` proofs.

The earlier dated reviews and remaining-proof plans are historical records;
this document describes the completed proof path.

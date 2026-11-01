import Splay.Accounting.ArticlePairingStageTransfers

namespace Splay.Accounting

open Splay.Lazy Splay.Lazy.Canonical Splay.Rank Splay.Tree.BST

/-- Every source actually enumerated in the internal worklist belongs to
the accessed owner. This follows from the implemented admissibility filter. -/
theorem ArticleRequestPreparation.admissibleWorklist_owner {n : ℕ} {params : Interface.Parameters}
    {snapshot : Snapshot n} {before : BST 0 n} {key : Fin n} {initial : Lazy.State n}
    (preparation : ArticleRequestPreparation params snapshot before key initial) {groups : List ℕ}
    (allBatches : ArticleRetainedPairingBatches snapshot before (Nat.le_refl n) key.val groups)
    (distinct : groups.Nodup) (rankZero : snapshot.rank (valuePos key) = 0)
    {item : ArticleAdmissibleSourceWorkItem key.val snapshot before params preparation.final}
    (member : item ∈ preparation.admissibleWorklist allBatches distinct rankZero) :
    item.source.owner = valuePos key := by
  obtain ⟨index, _, equal⟩ := List.mem_map.mp member
  subst item
  rw [(preparation.admissibleItem allBatches distinct rankZero index).property.2.1]
  exact ((preparation.mem_admissibleIndices allBatches index.val).mp index.property).1

/-- The complete actual pairing stage retains every shrinking physical ID.
Only blocks of the accessed owner may have their counters increased. -/
theorem ArticlePairingStage.shrinkingRefines {n : ℕ} {params : Interface.Parameters}
    {snapshot : Snapshot n} {before : BST 0 n} {key : Fin n} {kinds : List SplayStepKind}
    {initial : Lazy.State n} (stage : ArticlePairingStage params snapshot before key kinds initial) :
    State.ShrinkingRefinement (fun owner => owner = valuePos key) stage.preparation.final stage.final := by
  have internal := stage.internal.shrinkingRefines.mono (other := fun owner => owner = valuePos key) (by
    intro owner selected
    obtain ⟨item, member, equal⟩ := selected
    exact equal.symm.trans (stage.preparation.admissibleWorklist_owner stage.allBatches
      (zigZigDoubleGroupIndices_nodup kinds 0) stage.rankZero member))
  exact internal.trans (stage.boundary.shrinkingRefines.mono (fun _ impossible => impossible.elim))

end Splay.Accounting

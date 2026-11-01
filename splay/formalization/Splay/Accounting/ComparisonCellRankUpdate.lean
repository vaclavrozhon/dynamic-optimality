import Splay.Accounting.ComparisonRotationCuts
import Splay.Accounting.ArticleCanonicalRelocation
import Splay.Lazy.CellRankUpdate

namespace Splay.Accounting

open Splay.Rank Splay.Tree Splay.Lazy Splay.Lazy.Canonical JunctionBendReduction

/-- The concrete border preparation makes the final numeric rotation update
uniform on every relocated shrinking block. Surviving growing blocks share
their owner's shift, so all interval gaps can absorb the update silently. -/
theorem comparison_relocated_rankCompatible {n depth : ℕ} {params : Interface.Parameters}
    {before after splay : BST 0 n} (profile : BST.RotationCutProfile before after depth)
    {initial : Lazy.State n} {selected owners : Finset (Element n)} {cuts : Finset ℕ}
    (preparation : ArticleRelocationPreparation params initial selected owners cuts)
    (viewEq : initial.view = canonicalHeapView (Snapshot.ofTree before).withTruePriority splay)
    (ownerSubset : borderCutOwners (Snapshot.ofTree before).withTruePriority profile.cutSet profile.border ⊆ owners)
    (cutSubset : profile.cutSet ⊆ cuts)
    (valid : (preparation.final.relocateBlocks
      ((canonicalHeapView (Snapshot.ofTree after).withTruePriority splay).withRank preparation.final.view.rank)).Valid params) :
    let target := canonicalHeapView (Snapshot.ofTree after).withTruePriority splay
    let relocated := preparation.final.relocateBlocks (target.withRank preparation.final.view.rank)
    relocated.RankUpdateCompatible target (relocated.isolatedRankBlockShift target) := by
  dsimp only
  let target := canonicalHeapView (Snapshot.ofTree after).withTruePriority splay
  let transient := target.withRank preparation.final.view.rank
  let relocated := preparation.final.relocateBlocks transient
  have shiftedEq {first second : Element n} (same : SameCutCell profile.cutSet first second) :
      ((Snapshot.ofTree after).withTruePriority.rank first : ℤ) - preparation.final.view.rank first =
        ((Snapshot.ofTree after).withTruePriority.rank second : ℤ) - preparation.final.view.rank second := by
    rw [preparation.view_eq, viewEq]
    exact profile.doubled_shift_eq same
  apply State.rankUpdateCompatible_of_uniformChildShift valid target ⟨rfl, rfl, rfl, rfl, rfl⟩
  · intro block member growing element inside
    obtain ⟨old, oldMember, rfl⟩ := List.mem_map.mp member
    have oldGrowing : old.mode = .growing := by simpa only [Block.relocated_mode] using growing
    rw [Block.relocated_of_growing _ _ _ oldGrowing] at inside ⊢
    have same := preparation.growing_owner_sameCell (Snapshot.ofTree before).withTruePriority splay viewEq profile.border
      (fun cut member => (profile.border_spec cut member).1) ownerSubset oldMember oldGrowing inside
    exact (shiftedEq same).symm
  · intro block member _shrinking first firstIn second secondIn
    obtain ⟨old, oldMember, rfl⟩ := List.mem_map.mp member
    rw [Block.relocated_elements] at firstIn secondIn
    have same := preparation.all_blocks_sameCell (Snapshot.ofTree before).withTruePriority splay viewEq profile.border
      (fun cut member => (profile.border_spec cut member).1) ownerSubset cutSubset oldMember first firstIn second secondIn
    exact shiftedEq same

end Splay.Accounting

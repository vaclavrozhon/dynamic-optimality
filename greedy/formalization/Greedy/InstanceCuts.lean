import Greedy.InstanceConversions
import Greedy.GrowthStructural

/-! An old instance is retained or retired by a fresh cut; it cannot grow. -/

namespace Greedy.ClosedInstances

open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Lazy.Canonical
open GreedyMerge.OrderedBlocks GreedyMerge.Primitives GreedyMerge.HeapAllocation

theorem cutHeap_closed {n id : ℕ} {property : Frozen → Prop} (cut start : ℕ) (states : HeapSides n)
    (closed : HeapClosed id property states) (hereditary : ClosedFamilies.Hereditary property) (past : id < start) :
    HeapClosed id property (cutHeap cut start states).1 := by
  rw [cutHeap_eq_cutAllOwners]
  apply heap_old_descendants closed hereditary (after := cutAllOwners cut (cutNames start states) states) (fun _ _ => rfl)
  intro owner side block member same
  have below : block.id < cutNames start states owner side := by
    simp only [cutNames]
    omega
  obtain ⟨old, oldMem, sameId, descendant⟩ := cutList_old_descendant side cut (cutNames start states owner side)
    (states owner side).shrinking block member below
  exact ⟨owner, side, old, oldMem, sameId.symm.trans same, descendant⟩

theorem allocateCuts_closed {n id : ℕ} {property : Frozen → Prop} (cuts : List (ℕ × ℕ))
    (start : ℕ) (states : HeapSides n) (closed : HeapClosed id property states)
    (hereditary : ClosedFamilies.Hereditary property) (past : id < start) :
    HeapClosed id property (allocateCuts cuts start states).states := by
  induction cuts generalizing start states with
  | nil => exact closed
  | cons entry rest ih =>
      apply ih _ _ (cutHeap_closed entry.1 start states closed hereditary past)
      have advance : start ≤ (cutHeap entry.1 start states).2 := by
        dsimp only [cutHeap, GreedyMerge.FreshIds.freshCutStates]
        omega
      exact past.trans_le advance

theorem rebase_closed {n id : ℕ} {property : Frozen → Prop} (before after : BST 0 n)
    (states : HeapSides n) (closed : HeapClosed id property states) (hereditary : ClosedFamilies.Hereditary property) :
    HeapClosed id property (rebaseAll before after states) := by
  apply heap_old_descendants closed hereditary (after := rebaseAll before after states) (fun _ _ => rfl)
  intro owner side block member same
  obtain ⟨old, oldMem, rfl⟩ := List.mem_map.mp member
  exact ⟨owner, side, old, oldMem, same, rfl, rfl, List.Sublist.refl _⟩

theorem separateOuter_old_descendant (side : Bool) (cut fresh : ℕ) (state : SideState) (block : Frozen)
    (member : block ∈ (separateOuter side cut fresh state).1 ++ (separateOuter side cut fresh state).2)
    (past : block.id < fresh) : ∃ old, old ∈ state.shrinking ∧ block.id = old.id ∧ Descends block old := by
  apply cutList_old_descendant side cut fresh state.shrinking block _ past
  rcases List.mem_append.mp member with first | second <;> exact (List.mem_filter.mp ‹_›).1

end Greedy.ClosedInstances

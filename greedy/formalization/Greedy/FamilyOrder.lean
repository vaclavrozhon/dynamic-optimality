import Greedy.FamilyConversions
import ConcreteHistoryEdits
import ComparatorHistories

/-!
# Ordered histories across the whole heap

Within each family, different frozen fragments occupy disjoint intervals
of immutable join times. Local ordering and ordering between distinct
slots together imply the single-straddler property used in cancellation.
-/

namespace Greedy.FamilyOrder

open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Lazy.Canonical
open GreedyMerge.OrderedBlocks GreedyMerge.Primitives GreedyMerge.HeapAllocation
open GreedyMerge.FrozenHistory GreedyMerge.HistoryProcess GreedyForest

structure Ordered {Slot : Type*} (states : Slot → SideState) : Prop where
  localOrder : ∀ slot, GreedyMerge.HistoryProcess.Valid (states slot).shrinking
  between : ∀ first second, first ≠ second → ∀ left ∈ (states first).shrinking,
    ∀ right ∈ (states second).shrinking, Separated left right

theorem Ordered.local_steps {Slot : Type*} {before after : Slot → SideState}
    (ordered : Ordered before)
    (valid : ∀ slot, GreedyMerge.HistoryProcess.Valid (after slot).shrinking)
    (descendants : ∀ slot block, block ∈ (after slot).shrinking → ∃ old ∈ (before slot).shrinking, Descends block old) :
    Ordered after := by
  refine ⟨valid, ?_⟩
  intro first second different left leftMem right rightMem
  obtain ⟨oldLeft, oldLeftMem, leftDescends⟩ := descendants first left leftMem
  obtain ⟨oldRight, oldRightMem, rightDescends⟩ := descendants second right rightMem
  exact separated_descendants leftDescends rightDescends (ordered.between first second different oldLeft oldLeftMem oldRight oldRightMem)

theorem cut_ordered {Slot : Type*} (side : Slot → Bool) (cut : ℕ) (fresh : Slot → ℕ)
    (states : Slot → SideState) (ordered : Ordered states) :
    Ordered (fun slot => cutState (side slot) cut (fresh slot) (states slot)) := by
  apply ordered.local_steps
  · intro slot
    exact cutList_history_valid (side slot) cut (fresh slot) (states slot).shrinking (ordered.localOrder slot)
  · intro slot block member
    exact cutList_descends (side slot) cut (fresh slot) (states slot).shrinking block member

theorem erase_ordered {Slot : Type*} (key : Slot → ℕ) (states : Slot → SideState) (ordered : Ordered states) :
    Ordered (fun slot => eraseFrozenKey (key slot) (states slot)) := by
  apply ordered.local_steps
  · intro slot
    refine ⟨?_, ?_⟩
    · change ((states slot).shrinking.map (eraseMember (key slot))).Pairwise Separated
      rw [List.pairwise_map]
      exact (ordered.localOrder slot).1.imp (fun separated =>
        separated_descendants (erase_descends _ _) (erase_descends _ _) separated)
    · intro block member
      obtain ⟨old, oldMem, rfl⟩ := List.mem_map.mp member
      obtain ⟨orientation, history⟩ := (ordered.localOrder slot).2 old oldMem
      exact ⟨orientation, descends_preserves_history_orientation (erase_descends old (key slot)) orientation history⟩
  · intro slot block member
    obtain ⟨old, oldMem, rfl⟩ := List.mem_map.mp member
    exact ⟨old, oldMem, erase_descends old (key slot)⟩

noncomputable def allFrozen {Slot : Type*} [Fintype Slot] (states : Slot → SideState) : List Frozen :=
  Finset.univ.toList.flatMap (fun slot => (states slot).shrinking)

theorem allFrozen_valid {Slot : Type*} [Fintype Slot] (states : Slot → SideState) (ordered : Ordered states) :
    GreedyMerge.HistoryProcess.Valid (allFrozen states) := by
  classical
  have combine (slots : List Slot) (unique : slots.Nodup) :
      GreedyMerge.HistoryProcess.Valid (slots.flatMap (fun slot => (states slot).shrinking)) := by
    induction slots with
    | nil => exact ⟨by simp, by simp⟩
    | cons slot rest ih =>
        have tail := ih (List.nodup_cons.mp unique).2
        refine ⟨List.pairwise_append.mpr ⟨(ordered.localOrder slot).1, tail.1, ?_⟩, ?_⟩
        · intro left leftMem right rightMem
          obtain ⟨other, otherMem, rightMem⟩ := List.mem_flatMap.mp rightMem
          have different : slot ≠ other := by intro same; exact (List.nodup_cons.mp unique).1 (same ▸ otherMem)
          exact ordered.between slot other different left leftMem right rightMem
        · intro block member
          rcases List.mem_append.mp member with first | rest
          · exact (ordered.localOrder slot).2 block first
          · exact tail.2 block rest
  exact combine Finset.univ.toList (Finset.nodup_toList _)

theorem family_ordered {Slot : Type*} [Fintype Slot] (states : Slot → SideState) (ordered : Ordered states) (family : ℕ) :
    OrderedFamily (familyView family (allFrozen states)) :=
  GreedyMerge.HistoryProcess.family_ordered family _ (allFrozen_valid states ordered)

abbrev HeapOrdered {n : ℕ} (states : HeapSides n) := Ordered (table states)

theorem initial_ordered {n : ℕ} (snapshot : Snapshot n) (tree : BST 0 n) (K : ℤ) :
    HeapOrdered (GreedyMerge.InitialBlocks.state snapshot tree K) := by
  refine ⟨?_, ?_⟩
  · intro slot
    exact ⟨by simp [table, GreedyMerge.InitialBlocks.state], by simp [table, GreedyMerge.InitialBlocks.state]⟩
  · intro first second different left member
    simp [table, GreedyMerge.InitialBlocks.state] at member

end Greedy.FamilyOrder

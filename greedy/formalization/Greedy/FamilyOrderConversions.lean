import Greedy.FamilyOrder

/-! A newly frozen grower cannot interleave an older fragment of its family. -/

namespace Greedy.FamilyOrder

open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Lazy.Canonical
open GreedyMerge.OrderedBlocks GreedyMerge.Primitives GreedyMerge.HeapAllocation
open GreedyMerge.HistoryProcess GreedyMerge.ActualLinks

theorem convert_frozen_origin (owner family id base : ℕ) (state : SideState) (block : Frozen)
    (member : block ∈ (convert owner family id base state).shrinking) :
    block ∈ state.shrinking ∨ ∃ grower, state.grower = some grower ∧ block = freeze grower.id base grower := by
  cases present : state.grower with
  | none => exact Or.inl (by simpa [convert, present] using member)
  | some grower =>
      by_cases empty : grower.members = []
      · exact Or.inl (by simpa [convert, present, empty] using member)
      · simp only [convert, present, empty, ↓reduceIte, List.mem_append, List.mem_singleton] at member
        exact member.imp_right (fun equal => ⟨grower, rfl, equal⟩)

theorem convert_local_order (owner family id base : ℕ) (state : SideState)
    (ordered : GreedyMerge.HistoryProcess.Valid state.shrinking)
    (exclusive : ∀ block ∈ state.shrinking, ∀ grower, state.grower = some grower → block.family ≠ grower.family)
    (histories : ∀ grower, state.grower = some grower → HistMonotone true grower.members) :
    GreedyMerge.HistoryProcess.Valid (convert owner family id base state).shrinking := by
  cases present : state.grower with
  | none => simpa [convert, present] using ordered
  | some grower =>
      by_cases empty : grower.members = []
      · simpa [convert, present, empty] using ordered
      · simp only [convert, present, if_neg empty]
        refine ⟨List.pairwise_append.mpr ⟨ordered.1, List.pairwise_singleton _ _, ?_⟩, ?_⟩
        · intro old oldMem fresh freshMem
          have equal := List.mem_singleton.mp freshMem
          subst fresh
          exact Or.inl (exclusive old oldMem grower present)
        · intro block member
          rcases List.mem_append.mp member with old | fresh
          · exact ordered.2 block old
          · have equal := List.mem_singleton.mp fresh
            subst block
            exact ⟨true, histories grower present⟩

theorem conversions_ordered {slots next : ℕ} (owner family id base : Fin slots → ℕ)
    (selected : Fin slots → Bool) (states : Fin slots → SideState) (ordered : Ordered states)
    (names : FamilyNames.Inventory states next)
    (histories : ∀ slot grower, (states slot).grower = some grower → HistMonotone true grower.members) :
    Ordered (fun slot => if selected slot then convert (owner slot) (family slot) (id slot) (base slot) (states slot) else states slot) := by
  have origin (slot : Fin slots) (block : Frozen)
      (member : block ∈ (if selected slot then convert (owner slot) (family slot) (id slot) (base slot) (states slot) else states slot).shrinking) :
      block ∈ (states slot).shrinking ∨ ∃ grower, (states slot).grower = some grower ∧ block = freeze grower.id (base slot) grower := by
    split_ifs at member
    · exact convert_frozen_origin _ _ _ _ _ _ member
    · exact Or.inl member
  refine ⟨?_, ?_⟩
  · intro slot
    split_ifs
    · exact convert_local_order _ _ _ _ _ (ordered.localOrder slot)
        (fun block member grower present => names.sealed slot slot block grower member present) (histories slot)
    · exact ordered.localOrder slot
  · intro first second different left leftMem right rightMem
    rcases origin first left leftMem with leftOld | ⟨leftGrower, leftPresent, rfl⟩
    · rcases origin second right rightMem with rightOld | ⟨rightGrower, rightPresent, rfl⟩
      · exact ordered.between first second different left leftOld right rightOld
      · exact Or.inl (names.sealed first second left rightGrower leftOld rightPresent)
    · rcases origin second right rightMem with rightOld | ⟨rightGrower, rightPresent, rfl⟩
      · exact Or.inl (names.sealed second first right leftGrower rightOld leftPresent).symm
      · left
        intro equal
        exact different (names.growing first second leftGrower rightGrower leftPresent rightPresent equal)

theorem convertHeap_ordered {n next : ℕ} (rank : ℕ → ℕ) (selected : External n → Bool → Bool)
    (start : ℕ) (states : HeapSides n) (ordered : HeapOrdered states)
    (names : FamilyNames.HeapFamilyInventory states next) (histories : Histories states) :
    HeapOrdered (convertHeap rank selected start states).1 := by
  dsimp only [convertHeap]
  simp only [HeapOrdered, table_heap]
  apply conversions_ordered _ _ _ _ _ (table states) ordered names
  intro slot grower present
  exact (histories _ _).2 grower present

end Greedy.FamilyOrder

import Greedy.FamilyOrderConversions
import Greedy.FamilyPaid

/-! A fresh paid singleton has no other fragment in its new family. -/

namespace Greedy.FamilyOrder

open GreedyMerge.OrderedBlocks GreedyMerge.Primitives GreedyMerge.HistoryProcess

theorem insert_valid (left right : List Frozen) (fresh : Frozen)
    (ordered : GreedyMerge.HistoryProcess.Valid (left ++ right))
    (history : ∃ orientation, HistMonotone orientation fresh.members)
    (separated : ∀ old ∈ left ++ right, Separated old fresh) :
    GreedyMerge.HistoryProcess.Valid (left ++ fresh :: right) := by
  obtain ⟨leftOrder, rightOrder, cross⟩ := List.pairwise_append.mp ordered.1
  refine ⟨List.pairwise_append.mpr ⟨leftOrder, List.pairwise_cons.mpr ⟨?_, rightOrder⟩, ?_⟩, ?_⟩
  · intro old member
    exact separated_symm (separated old (List.mem_append_right _ member))
  · intro old member later laterMem
    rcases List.mem_cons.mp laterMem with rfl | rightMem
    · exact separated old (List.mem_append_left _ member)
    · exact cross old member later rightMem
  · intro block member
    rcases List.mem_append.mp member with before | later
    · exact ordered.2 block (List.mem_append_left _ before)
    · rcases List.mem_cons.mp later with rfl | after
      · exact history
      · exact ordered.2 block (List.mem_append_right _ after)

theorem installPaid_local_order (owner : ℕ) (side : Bool) (splitStart id family base : ℕ)
    (entry : Entry) (state : SideState) (ordered : GreedyMerge.HistoryProcess.Valid state.shrinking)
    (fresh : ∀ block ∈ state.shrinking, block.family < family) :
    GreedyMerge.HistoryProcess.Valid (installPaid owner side splitStart id family base entry state).shrinking := by
  let parts := separateOuter side entry.key splitStart state
  have perm : (parts.1 ++ parts.2).Perm (cutList side entry.key splitStart state.shrinking) :=
    List.filter_append_perm _ _
  have partitioned := (Edit.perm perm).valid (cutList_history_valid side entry.key splitStart state.shrinking ordered)
  have inserted := insert_valid parts.1 parts.2 (singleton id family owner base entry) partitioned
    ⟨true, List.pairwise_singleton _ _⟩ ?_
  · simpa only [installPaid, List.append_assoc, List.singleton_append] using inserted
  intro old member
  obtain ⟨original, originalMem, descendant⟩ := separateOuter_descends side entry.key splitStart state old member
  have bound := fresh original originalMem
  left
  change old.family ≠ family
  rw [descendant.1]
  omega

theorem installPaid_origin (owner : ℕ) (side : Bool) (splitStart id family base : ℕ)
    (entry : Entry) (state : SideState) (block : Frozen)
    (member : block ∈ (installPaid owner side splitStart id family base entry state).shrinking) :
    (∃ old ∈ state.shrinking, Descends block old) ∨ block = singleton id family owner base entry := by
  change block ∈ (separateOuter side entry.key splitStart state).1 ++ [singleton id family owner base entry] ++
    (separateOuter side entry.key splitStart state).2 at member
  rcases List.mem_append.mp member with first | last
  · rcases List.mem_append.mp first with old | new
    · exact Or.inl (separateOuter_descends side entry.key splitStart state block (List.mem_append_left _ old))
    · exact Or.inr (List.mem_singleton.mp new)
  · exact Or.inl (separateOuter_descends side entry.key splitStart state block (List.mem_append_right _ last))

theorem installPaid_ordered {slots next : ℕ} (states : Fin slots → SideState) (selected : Fin slots)
    (owner : ℕ) (side : Bool) (splitStart id family base : ℕ) (entry : Entry)
    (ordered : Ordered states) (names : FamilyNames.Inventory states next) (fresh : next ≤ family) :
    Ordered (Function.update states selected (installPaid owner side splitStart id family base entry (states selected))) := by
  have bound (slot : Fin slots) (block : Frozen) (member : block ∈ (states slot).shrinking) : block.family < family :=
    (names.below slot block.family (FamilyNames.frozen_mem _ _ member)).trans_le fresh
  have cross (other : Fin slots) (different : selected ≠ other) (left right : Frozen)
      (leftMem : left ∈ (installPaid owner side splitStart id family base entry (states selected)).shrinking)
      (rightMem : right ∈ (states other).shrinking) : Separated left right := by
    rcases installPaid_origin owner side splitStart id family base entry _ left leftMem with ⟨old, oldMem, descendant⟩ | rfl
    · exact separated_descendants descendant (descends_refl _) (ordered.between selected other different old oldMem right rightMem)
    · left
      change family ≠ right.family
      have older := bound other right rightMem
      omega
  refine ⟨?_, ?_⟩
  · intro slot
    by_cases same : slot = selected
    · subst slot
      rw [Function.update_self]
      exact installPaid_local_order owner side splitStart id family base entry _ (ordered.localOrder selected) (bound selected)
    · rw [Function.update_of_ne same]
      exact ordered.localOrder slot
  · intro first second different left leftMem right rightMem
    by_cases firstEq : first = selected
    · subst first
      rw [Function.update_self] at leftMem
      rw [Function.update_of_ne different.symm] at rightMem
      exact cross second different left right leftMem rightMem
    · rw [Function.update_of_ne firstEq] at leftMem
      by_cases secondEq : second = selected
      · subst second
        rw [Function.update_self] at rightMem
        exact separated_symm (cross first (Ne.symm firstEq) right left rightMem leftMem)
      · rw [Function.update_of_ne secondEq] at rightMem
        exact ordered.between first second different left leftMem right rightMem

theorem single_convert_ordered {slots next : ℕ} (states : Fin slots → SideState) (selected : Fin slots)
    (owner fresh base : ℕ) (ordered : Ordered states) (names : FamilyNames.Inventory states next)
    (histories : ∀ slot grower, (states slot).grower = some grower → HistMonotone true grower.members) :
    Ordered (Function.update states selected (convert owner fresh fresh base (states selected))) := by
  have converted := conversions_ordered (fun _ => owner) (fun _ => fresh) (fun _ => fresh) (fun _ => base)
    (fun slot => decide (slot = selected)) states ordered names histories
  have equal : (fun slot => if decide (slot = selected) then convert owner fresh fresh base (states slot) else states slot) =
      Function.update states selected (convert owner fresh fresh base (states selected)) := by
    funext slot
    by_cases same : slot = selected <;> simp [same]
  rwa [equal] at converted

theorem freshPaidSlot_ordered {slots start : ℕ} (slot : Fin slots) (owner base : ℕ) (side : Bool)
    (entry : Entry) (states : Fin slots → SideState) (ordered : Ordered states) (names : FamilyNames.Inventory states start)
    (histories : ∀ slot grower, (states slot).grower = some grower → HistMonotone true grower.members) :
    Ordered (GreedyMerge.FreshIds.freshPaidSlot slot owner base side start entry states).1 := by
  let converted := convert owner start start base (states slot)
  let paid := start+1+2*converted.shrinking.length
  have first := single_convert_ordered states slot owner start base ordered names histories
  have fresh := FamilyNames.convert_inventory states slot owner start base names (le_refl _)
  have second := installPaid_ordered (Function.update states slot converted) slot owner side (start+1) paid paid base entry first fresh
    (show start+1 ≤ paid by dsimp [paid]; omega)
  simp only [Function.update_self, Function.update_idem] at second
  exact second

end Greedy.FamilyOrder

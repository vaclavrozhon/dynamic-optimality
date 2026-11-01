import Greedy.ClosedFamilies
import Greedy.FamilyOrderPaid

/-! Paid insertions create different families and preserve closed-family properties. -/

namespace Greedy.ClosedFamilies

open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Lazy.Canonical
open GreedyMerge.OrderedBlocks GreedyMerge.Primitives GreedyMerge.HeapAllocation

theorem single_convert_closed {slots family : ℕ} {property : Frozen → Prop}
    (states : Fin slots → SideState) (selected : Fin slots) (owner fresh base : ℕ)
    (closed : Closed family property states) (past : family < fresh) :
    Closed family property (Function.update states selected (convert owner fresh fresh base (states selected))) := by
  have converted := conversions_closed family property (fun _ => owner) (fun _ => fresh) (fun _ => fresh) (fun _ => base)
    (fun slot => decide (slot = selected)) states closed (fun _ => past)
  have equal : (fun slot => if decide (slot = selected) then convert owner fresh fresh base (states slot) else states slot) =
      Function.update states selected (convert owner fresh fresh base (states selected)) := by
    funext slot
    by_cases same : slot = selected <;> simp [same]
  rwa [equal] at converted

theorem installPaid_closed {slots family : ℕ} {property : Frozen → Prop}
    (states : Fin slots → SideState) (selected : Fin slots) (owner : ℕ) (side : Bool)
    (splitStart id paidFamily base : ℕ) (entry : Entry) (closed : Closed family property states)
    (hereditary : Hereditary property) (past : family < paidFamily) :
    Closed family property (Function.update states selected
      (installPaid owner side splitStart id paidFamily base entry (states selected))) := by
  apply closed.additions hereditary
  · intro slot grower present
    refine Or.inl ⟨slot, grower, ?_, rfl⟩
    by_cases same : slot = selected
    · subst slot
      simpa only [Function.update_self, installPaid] using present
    · simpa only [Function.update_of_ne same] using present
  · intro slot block member
    by_cases same : slot = selected
    · subst slot
      rw [Function.update_self] at member
      rcases FamilyOrder.installPaid_origin owner side splitStart id paidFamily base entry _ block member with ⟨old, oldMem, descendant⟩ | rfl
      · exact Or.inl ⟨selected, old, oldMem, descendant⟩
      · exact Or.inr past
    · rw [Function.update_of_ne same] at member
      exact Or.inl ⟨slot, block, member, descends_refl _⟩

theorem freshPaidSlot_closed {slots family : ℕ} {property : Frozen → Prop} (slot : Fin slots)
    (owner base : ℕ) (side : Bool) (start : ℕ) (entry : Entry) (states : Fin slots → SideState)
    (closed : Closed family property states) (hereditary : Hereditary property) (past : family < start) :
    Closed family property (GreedyMerge.FreshIds.freshPaidSlot slot owner base side start entry states).1 := by
  let converted := convert owner start start base (states slot)
  let paid := start+1+2*converted.shrinking.length
  have first := single_convert_closed states slot owner start base closed past
  have second := installPaid_closed (Function.update states slot converted) slot owner side (start+1) paid paid base entry first hereditary
    (show family < paid by dsimp [paid]; omega)
  simp only [Function.update_self, Function.update_idem] at second
  exact second

theorem restorePort_closed {n family : ℕ} {property : Frozen → Prop} (snapshot : Snapshot n) (tree : BST 0 n)
    (record : External n) (makeEntry : External n → Entry) (start : ℕ) (states : HeapSides n)
    (closed : HeapClosed family property states) (hereditary : Hereditary property) (past : family < start) :
    HeapClosed family property (restorePort snapshot tree (portNames snapshot tree record start states) makeEntry record states).1 := by
  cases parent : canonicalParent snapshot tree record with
  | none => simpa only [restorePort, parent] using closed
  | some owner =>
      let side := decide (record.val < owner.val)
      let slot := encode n (owner, side)
      have supplied := freshPaidSlot_closed slot owner.val (snapshot.rank owner) side start (makeEntry owner) (table states) closed hereditary past
      have receiver : table states slot = states owner side := by simp [table, slot]
      have mapped : HeapClosed family property
          (heap (GreedyMerge.FreshIds.freshPaidSlot slot owner.val (snapshot.rank owner) side start (makeEntry owner) (table states)).1) := by
        simpa only [HeapClosed, table_heap] using supplied
      dsimp only [GreedyMerge.FreshIds.freshPaidSlot] at mapped
      rw [receiver, heap_update] at mapped
      simpa only [restorePort, portNames, parent, GreedyMerge.FreshIds.freshPaidInsertion] using mapped

theorem restoration_closed {n family : ℕ} {property : Frozen → Prop} (snapshot : Snapshot n) (tree : BST 0 n)
    (reader : ℕ → HeapSides n → External n → External n → Entry) (ports : List (External n))
    (stage start : ℕ) (states : HeapSides n) (closed : HeapClosed family property states)
    (hereditary : Hereditary property) (past : family < start) :
    HeapClosed family property (freshRestorePorts snapshot tree reader ports stage start states).states := by
  induction ports generalizing stage start states with
  | nil => exact closed
  | cons record rest ih =>
      exact ih (stage+1) _ _ (restorePort_closed snapshot tree record (reader stage states record) start states closed hereditary past)
        (past.trans_le (restoreNext_monotone snapshot tree record start states))

end Greedy.ClosedFamilies

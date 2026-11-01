import Greedy.InstanceTransfer
import Greedy.ClosedPaid

/-! Paid restoration inserts fresh ids and cannot revive an old instance. -/

namespace Greedy.ClosedInstances

open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Lazy.Canonical
open GreedyMerge.OrderedBlocks GreedyMerge.Primitives GreedyMerge.HeapAllocation

theorem single_convert_closed {slots id : ℕ} {property : Frozen → Prop}
    (states : Fin slots → SideState) (selected : Fin slots) (owner fresh base : ℕ)
    (closed : Closed id property states) (past : id < fresh) :
    Closed id property (Function.update states selected (convert owner fresh fresh base (states selected))) := by
  have converted := conversions_closed id property (fun _ => owner) (fun _ => fresh) (fun _ => fresh) (fun _ => base)
    (fun slot => decide (slot = selected)) states closed (fun _ => past)
  have equal : (fun slot => if decide (slot = selected) then convert owner fresh fresh base (states slot) else states slot) =
      Function.update states selected (convert owner fresh fresh base (states selected)) := by
    funext slot
    by_cases same : slot = selected <;> simp [same]
  rwa [equal] at converted

theorem installPaid_closed {slots id : ℕ} {property : Frozen → Prop}
    (states : Fin slots → SideState) (selected : Fin slots) (owner : ℕ) (side : Bool)
    (splitStart paidId paidFamily base : ℕ) (entry : Entry) (closed : Closed id property states)
    (hereditary : ClosedFamilies.Hereditary property) (pastSplit : id < splitStart) (pastPaid : id < paidId) :
    Closed id property (Function.update states selected
      (installPaid owner side splitStart paidId paidFamily base entry (states selected))) := by
  refine ⟨?_, ?_⟩
  · intro slot grower present
    apply closed.growing slot grower
    by_cases same : slot = selected
    · subst slot
      simpa only [Function.update_self, installPaid] using present
    · simpa only [Function.update_of_ne same] using present
  · intro slot block member sameId
    by_cases same : slot = selected
    · subst slot
      rw [Function.update_self] at member
      change block ∈ (separateOuter side entry.key splitStart (states selected)).1 ++
        [singleton paidId paidFamily owner base entry] ++ (separateOuter side entry.key splitStart (states selected)).2 at member
      have inherited (oldMem : block ∈ (separateOuter side entry.key splitStart (states selected)).1 ++
          (separateOuter side entry.key splitStart (states selected)).2) : property block := by
        obtain ⟨old, oldMem, oldId, descendant⟩ := separateOuter_old_descendant side entry.key splitStart (states selected) block oldMem
          (by omega)
        exact hereditary descendant (closed.frozen selected old oldMem (oldId.symm.trans sameId))
      rcases List.mem_append.mp member with first | last
      · rcases List.mem_append.mp first with old | paid
        · exact inherited (List.mem_append_left _ old)
        · have equal := List.mem_singleton.mp paid
          subst block
          change paidId = id at sameId
          omega
      · exact inherited (List.mem_append_right _ last)
    · rw [Function.update_of_ne same] at member
      exact closed.frozen slot block member sameId

theorem freshPaidSlot_closed {slots id : ℕ} {property : Frozen → Prop} (slot : Fin slots)
    (owner base : ℕ) (side : Bool) (start : ℕ) (entry : Entry) (states : Fin slots → SideState)
    (closed : Closed id property states) (hereditary : ClosedFamilies.Hereditary property) (past : id < start) :
    Closed id property (GreedyMerge.FreshIds.freshPaidSlot slot owner base side start entry states).1 := by
  let converted := convert owner start start base (states slot)
  let paid := start+1+2*converted.shrinking.length
  have first := single_convert_closed states slot owner start base closed past
  have second := installPaid_closed (Function.update states slot converted) slot owner side (start+1) paid paid base entry first hereditary
    (by omega) (show id < paid by dsimp [paid]; omega)
  simp only [Function.update_self, Function.update_idem] at second
  exact second

theorem restorePort_closed {n id : ℕ} {property : Frozen → Prop} (snapshot : Snapshot n) (tree : BST 0 n)
    (record : External n) (makeEntry : External n → Entry) (start : ℕ) (states : HeapSides n)
    (closed : HeapClosed id property states) (hereditary : ClosedFamilies.Hereditary property) (past : id < start) :
    HeapClosed id property (restorePort snapshot tree (portNames snapshot tree record start states) makeEntry record states).1 := by
  cases parent : canonicalParent snapshot tree record with
  | none => simpa only [restorePort, parent] using closed
  | some owner =>
      let side := decide (record.val < owner.val)
      let slot := encode n (owner, side)
      have supplied := freshPaidSlot_closed slot owner.val (snapshot.rank owner) side start (makeEntry owner) (table states) closed hereditary past
      have receiver : table states slot = states owner side := by simp [table, slot]
      have mapped : HeapClosed id property
          (heap (GreedyMerge.FreshIds.freshPaidSlot slot owner.val (snapshot.rank owner) side start (makeEntry owner) (table states)).1) := by
        simpa only [HeapClosed, table_heap] using supplied
      dsimp only [GreedyMerge.FreshIds.freshPaidSlot] at mapped
      rw [receiver, heap_update] at mapped
      simpa only [restorePort, portNames, parent, GreedyMerge.FreshIds.freshPaidInsertion] using mapped

theorem restoration_closed {n id : ℕ} {property : Frozen → Prop} (snapshot : Snapshot n) (tree : BST 0 n)
    (reader : ℕ → HeapSides n → External n → External n → Entry) (ports : List (External n))
    (stage start : ℕ) (states : HeapSides n) (closed : HeapClosed id property states)
    (hereditary : ClosedFamilies.Hereditary property) (past : id < start) :
    HeapClosed id property (freshRestorePorts snapshot tree reader ports stage start states).states := by
  induction ports generalizing stage start states with
  | nil => exact closed
  | cons record rest ih =>
      exact ih (stage+1) _ _ (restorePort_closed snapshot tree record (reader stage states record) start states closed hereditary past)
        (past.trans_le (restoreNext_monotone snapshot tree record start states))

end Greedy.ClosedInstances

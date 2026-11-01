import StateLabels
import ActualLinkState
import Mathlib.Data.Nat.Pairing

/-!
Construct the starting block state of an arbitrary actual canonical heap.
Every owner has two persistent growers containing its actual children in
outward key order. No initial cover, ordering, soundness or history premise
is accepted. Ticket times use an injective monotone pairing so every entry
has its own immutable chronological identifier.
-/

namespace GreedyMerge.InitialBlocks

open OrderedBlocks Primitives BlockCoverage
open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Lazy.Canonical Splay.Analysis

def slot {n : ℕ} (owner : External n) (side : Bool) : ℕ :=
  2 * owner.val + side.toNat

def position {n : ℕ} (side : Bool) (record : External n) : ℕ :=
  if side then 2*n-record.val else record.val

def ticket {n : ℕ} (owner : External n) (side : Bool) (record : External n) : ℕ :=
  Nat.pair (slot owner side) (position side record)

def allRecords (n : ℕ) : List (External n) := List.ofFn (fun record : External n => record)

def sideKey (owner : ℕ) (side : Bool) (key : ℕ) : Prop :=
  if side then key < owner else owner < key

noncomputable def children {n : ℕ} (snapshot : Snapshot n) (tree : BST 0 n)
    (owner : External n) (side : Bool) : List (External n) := by
  classical
  exact (if side then (allRecords n).reverse else allRecords n).filter
    (fun record => canonicalParent snapshot tree record = some owner ∧ sideKey owner.val side record.val)

theorem mem_children {n : ℕ} (snapshot : Snapshot n) (tree : BST 0 n)
    (owner record : External n) (side : Bool) :
    record ∈ children snapshot tree owner side ↔
      canonicalParent snapshot tree record = some owner ∧ sideKey owner.val side record.val := by
  classical
  have present : record ∈ allRecords n := List.mem_ofFn.mpr ⟨record, rfl⟩
  cases side <;> simp [children, present]

theorem children_ordered {n : ℕ} (snapshot : Snapshot n) (tree : BST 0 n)
    (owner : External n) (side : Bool) :
    (children snapshot tree owner side).Pairwise
      (fun first second => if side then second.val < first.val else first.val < second.val) := by
  classical
  have ascending : (allRecords n).Pairwise (fun first second => first.val < second.val) :=
    List.pairwise_ofFn.mpr (fun _ _ less => less)
  have descending : (allRecords n).reverse.Pairwise (fun first second => second.val < first.val) := by
    simpa only [List.pairwise_reverse] using ascending
  cases side
  · exact ascending.filter _
  · exact descending.filter _

noncomputable def rawLabel {n : ℕ} (snapshot : Snapshot n) (tree : BST 0 n) (K : ℤ)
    (record : External n) : ℤ :=
  match canonicalParent snapshot tree record with
  | none => K
  | some owner => contractedGap (snapshot.rank record - snapshot.rank owner)

noncomputable def entry {n : ℕ} (snapshot : Snapshot n) (tree : BST 0 n) (K : ℤ)
    (owner : External n) (side : Bool) (record : External n) : Entry :=
  ⟨record.val, ticket owner side record, rawLabel snapshot tree K record, rawLabel snapshot tree K owner⟩

noncomputable def state {n : ℕ} (snapshot : Snapshot n) (tree : BST 0 n) (K : ℤ) : States n :=
  fun owner side => ⟨[], some ⟨slot owner side, slot owner side, owner.val,
    (children snapshot tree owner side).map (entry snapshot tree K owner side)⟩⟩

theorem state_entries {n : ℕ} (snapshot : Snapshot n) (tree : BST 0 n) (K : ℤ)
    (owner : External n) (side : Bool) :
    entries (state snapshot tree K owner side) =
      (children snapshot tree owner side).map (entry snapshot tree K owner side) := rfl

theorem state_valid {n : ℕ} (snapshot : Snapshot n) (tree : BST 0 n) (K : ℤ) :
    ∀ owner side, Valid owner.val side (state snapshot tree K owner side) := by
  intro owner side
  refine ⟨?_, ?_, ?_⟩
  · rw [state_entries, List.pairwise_map]
    exact children_ordered snapshot tree owner side
  · intro actual member
    rw [state_entries] at member
    obtain ⟨record, present, rfl⟩ := List.mem_map.mp member
    exact ((mem_children snapshot tree owner record side).mp present).2
  · intro grower same
    have equal := Option.some.inj same
    exact (congrArg Grower.creator equal).symm

theorem state_sound {n : ℕ} (snapshot : Snapshot n) (tree : BST 0 n) (K : ℤ) :
    Sound snapshot tree (state snapshot tree K) := by
  intro owner side actual member
  rw [state_entries] at member
  obtain ⟨record, present, rfl⟩ := List.mem_map.mp member
  exact ⟨record, rfl, ((mem_children snapshot tree owner record side).mp present).1⟩

theorem state_complete {n : ℕ} (snapshot : Snapshot n) (tree : BST 0 n) (K : ℤ) :
    Complete snapshot tree (state snapshot tree K) := by
  intro record owner parent _
  let side := decide (record.val < owner.val)
  have separate : record.val ≠ owner.val := by
    intro equal
    have same : record = owner := Fin.ext equal
    have lower := rank_canonicalParent_lt snapshot tree parent
    rw [same] at lower
    omega
  have correctSide : sideKey owner.val side record.val := by
    unfold sideKey side
    split_ifs with before
    · simpa only [decide_eq_true_eq] using before
    · have notBefore : ¬record.val < owner.val := by simpa only [decide_eq_true_eq] using before
      omega
  refine ⟨side, entry snapshot tree K owner side record, ?_, rfl⟩
  rw [state_entries]
  exact List.mem_map.mpr ⟨record, (mem_children snapshot tree owner record side).mpr ⟨parent, correctSide⟩, rfl⟩

theorem state_persistent {n : ℕ} (snapshot : Snapshot n) (tree : BST 0 n) (K : ℤ) :
    ActualLinks.Persistent (state snapshot tree K) := by
  intro owner side
  rfl

theorem ticket_ordered {n : ℕ} (owner : External n) (side : Bool) (first second : External n)
    (outwardOrder : if side then second.val < first.val else first.val < second.val) :
    ticket owner side first < ticket owner side second := by
  apply Nat.pair_lt_pair_right
  cases side <;> simp only [position, Bool.false_eq_true, if_false, if_true] at outwardOrder ⊢
  · exact outwardOrder
  · have firstBound := first.isLt
    have secondBound := second.isLt
    omega

theorem state_history {n : ℕ} (snapshot : Snapshot n) (tree : BST 0 n) (K : ℤ)
    (owner : External n) (side : Bool) :
    HistMonotone true (growerEntries (state snapshot tree K owner side).grower) := by
  change ((children snapshot tree owner side).map (entry snapshot tree K owner side)).Pairwise _
  rw [List.pairwise_map]
  apply (children_ordered snapshot tree owner side).imp
  intro first second order
  exact ticket_ordered owner side first second order

theorem slot_injective {n : ℕ} (first second : External n) (firstSide secondSide : Bool)
    (equal : slot first firstSide = slot second secondSide) :
    first = second ∧ firstSide = secondSide := by
  cases firstSide <;> cases secondSide <;> simp only [slot, Bool.toNat_false, Bool.toNat_true] at equal
  · exact ⟨Fin.ext (by omega), rfl⟩
  · omega
  · omega
  · exact ⟨Fin.ext (by omega), rfl⟩

theorem ticket_injective {n : ℕ} (firstOwner secondOwner firstRecord secondRecord : External n)
    (firstSide secondSide : Bool)
    (equal : ticket firstOwner firstSide firstRecord = ticket secondOwner secondSide secondRecord) :
    firstOwner = secondOwner ∧ firstSide = secondSide ∧ firstRecord = secondRecord := by
  obtain ⟨sameSlot, samePosition⟩ := Nat.pair_eq_pair.mp equal
  obtain ⟨rfl, rfl⟩ := slot_injective firstOwner secondOwner firstSide secondSide sameSlot
  refine ⟨rfl, rfl, Fin.ext ?_⟩
  cases firstSide <;> simp only [position, Bool.false_eq_true, if_false, if_true] at samePosition
  · exact samePosition
  · have firstBound := firstRecord.isLt
    have secondBound := secondRecord.isLt
    omega

end GreedyMerge.InitialBlocks

#print axioms GreedyMerge.InitialBlocks.state_valid
#print axioms GreedyMerge.InitialBlocks.state_complete
#print axioms GreedyMerge.InitialBlocks.state_history
#print axioms GreedyMerge.InitialBlocks.ticket_injective

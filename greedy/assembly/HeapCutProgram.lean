import HeapFreshAllocation
import FreshCutProgram

/-! Instantiate the existing rank-cut program with a concrete fresh name
supply computed from its own intermediate states. The returned birth
journal, not the reserved counter, equals the existing charged cost. -/

namespace GreedyMerge.HeapAllocation

open OrderedBlocks FreshIds
open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Lazy.Canonical

theorem cutJournal_length {n : ℕ} (cut start : ℕ) (states : HeapSides n) :
    (freshCutJournal cut start (table states)).length = allOwnerCutBirths states cut := by
  rw [freshCutJournal_length]
  have changeIndex := (encode n).symm.sum_comp
    (fun place : Place n => cutListBirths cut (states place.1 place.2).shrinking)
  change (∑ slot : Slot n, cutListBirths cut
    (states ((encode n).symm slot).1 ((encode n).symm slot).2).shrinking) = _
  rw [changeIndex, Fintype.sum_prod_type]
  simp [allOwnerCutBirths, ownerCutBirths, Nat.add_comm]

theorem prepareCuts_shift {n : ℕ} (names : NameSupply n) (cuts : List (ℕ × ℕ))
    (offset stage : ℕ) (states : HeapSides n) :
    prepareCuts names cuts (stage+offset) states =
      prepareCuts (fun i => names (i+offset)) cuts stage states := by
  induction cuts generalizing stage states with
  | nil => rfl
  | cons entry rest ih =>
      simp only [prepareCuts]
      rw [show stage+offset+1=(stage+1)+offset by omega, ih]

structure CutProgram (n : ℕ) where
  names : NameSupply n
  states : HeapSides n
  next : ℕ
  born : List ℕ

noncomputable def allocateCuts {n : ℕ} : List (ℕ × ℕ) → ℕ → HeapSides n → CutProgram n
  | [], start, states => ⟨fun _ _ _ => 0, states, start, []⟩
  | entry :: rest, start, states =>
      let step := cutHeap entry.1 start states
      let tail := allocateCuts rest step.2 step.1
      ⟨(fun stage => match stage with
          | 0 => cutNames start states
          | i+1 => tail.names i),
        tail.states, tail.next, freshCutJournal entry.1 start (table states) ++ tail.born⟩

theorem allocateCuts_eq {n : ℕ} (cuts : List (ℕ × ℕ)) (start : ℕ) (states : HeapSides n) :
    prepareCuts (allocateCuts cuts start states).names cuts 0 states =
      ((allocateCuts cuts start states).states, (allocateCuts cuts start states).born.length) := by
  induction cuts generalizing start states with
  | nil => rfl
  | cons entry rest ih =>
      let step := cutHeap entry.1 start states
      let tail := allocateCuts rest step.2 step.1
      have shifted : prepareCuts (allocateCuts (entry::rest) start states).names rest 1 step.1 =
          prepareCuts tail.names rest 0 step.1 := by
        rw [show 1=0+1 by omega, prepareCuts_shift]
        rfl
      change ((prepareCuts (allocateCuts (entry::rest) start states).names rest 1
          (cutAllOwners entry.1 (cutNames start states) states)).1,
        allOwnerCutBirths states entry.1 +
          (prepareCuts (allocateCuts (entry::rest) start states).names rest 1
          (cutAllOwners entry.1 (cutNames start states) states)).2) = _
      rw [← cutHeap_eq_cutAllOwners, shifted, ih]
      simp only [allocateCuts, List.length_append, cutJournal_length, step]

theorem allocateCuts_inventory {n : ℕ} (cuts : List (ℕ × ℕ)) (start : ℕ)
    (states : HeapSides n) (inventory : HeapInventory states start) :
    HeapInventory (allocateCuts cuts start states).states (allocateCuts cuts start states).next := by
  induction cuts generalizing start states with
  | nil => exact inventory
  | cons entry rest ih => exact ih _ _ (cutHeap_inventory entry.1 start states inventory)

theorem allocateCuts_next {n : ℕ} (cuts : List (ℕ × ℕ)) (start : ℕ) (states : HeapSides n) :
    start ≤ (allocateCuts cuts start states).next := by
  induction cuts generalizing start states with
  | nil => exact le_refl _
  | cons entry rest ih => exact (Nat.le_add_right _ _).trans (ih _ _)

theorem allocateCuts_new {n : ℕ} (cuts : List (ℕ × ℕ)) (start : ℕ) (states : HeapSides n)
    (id : ℕ) (member : id ∈ (allocateCuts cuts start states).born) : start ≤ id := by
  induction cuts generalizing start states with
  | nil => simp [allocateCuts] at member
  | cons entry rest ih =>
      rcases List.mem_append.mp member with head | tail
      · exact freshCutJournal_new entry.1 start (table states) id head
      · exact (Nat.le_add_right _ _).trans (ih _ _ tail)

theorem allocateCuts_before_next {n : ℕ} (cuts : List (ℕ × ℕ)) (start : ℕ)
    (states : HeapSides n) (inventory : HeapInventory states start)
    (id : ℕ) (member : id ∈ (allocateCuts cuts start states).born) :
    id < (allocateCuts cuts start states).next := by
  induction cuts generalizing start states with
  | nil => simp [allocateCuts] at member
  | cons entry rest ih =>
      rcases List.mem_append.mp member with head | tail
      · exact lt_of_lt_of_le (freshCutJournal_before_next (sides n) entry.1 start
          (table states) inventory id head) (allocateCuts_next rest _ _)
      · exact ih _ _ (cutHeap_inventory entry.1 start states inventory) tail

theorem allocateCuts_unique {n : ℕ} (cuts : List (ℕ × ℕ)) (start : ℕ)
    (states : HeapSides n) (inventory : HeapInventory states start) :
    (allocateCuts cuts start states).born.Nodup := by
  induction cuts generalizing start states with
  | nil => simp [allocateCuts]
  | cons entry rest ih =>
      apply List.nodup_append.mpr
      refine ⟨freshCutJournal_unique (sides n) entry.1 start (table states) inventory,
        ih _ _ (cutHeap_inventory entry.1 start states inventory), ?_⟩
      intro first firstMember second secondMember equal
      have old := freshCutJournal_before_next (sides n) entry.1 start (table states) inventory first firstMember
      have new := allocateCuts_new rest _ _ second secondMember
      change (freshCutStates (sides n) entry.1 start (table states)).2 ≤ second at new
      omega

end GreedyMerge.HeapAllocation

#print axioms GreedyMerge.HeapAllocation.allocateCuts_eq
#print axioms GreedyMerge.HeapAllocation.allocateCuts_inventory
#print axioms GreedyMerge.HeapAllocation.allocateCuts_unique

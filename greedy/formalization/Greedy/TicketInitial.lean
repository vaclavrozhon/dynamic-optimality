import Greedy.TicketRestoration

/-! Initial canonical children receive their actual initial membership names. -/

namespace Greedy.TicketJournal

open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Lazy.Canonical
open GreedyMerge.OrderedBlocks GreedyMerge.Primitives GreedyMerge.ActualLinks
open WinnerCredit

noncomputable def install {n : ℕ} (parent : External n → Option (External n))
    (name : External n → External n → MembershipPointer.Ticket) : List (External n) → List (Action n)
  | [] => []
  | record :: rest =>
      (match parent record with
       | none => []
       | some owner => [.entry record owner .ordinary (name record owner)]) ++ install parent name rest

theorem install_erases {n : ℕ} (parent : External n → Option (External n))
    (name : External n → External n → MembershipPointer.Ticket) (records : List (External n)) :
    erase (install parent name records) = InitialJournal.install parent records := by
  induction records with
  | nil => rfl
  | cons record rest ih =>
      cases relation : parent record <;> simp [install, relation, InitialJournal.install, erase, eraseOne] at ih ⊢ <;> exact ih

theorem install_administrative {n : ℕ} (parent : External n → Option (External n))
    (name : External n → External n → MembershipPointer.Ticket) (records : List (External n)) :
    Administrative (install parent name records) := by
  induction records with
  | nil => simp [install, Administrative]
  | cons record rest ih =>
      rw [install, administrative_append]
      refine ⟨?_, ih⟩
      cases relation : parent record <;> simp [Administrative]

theorem install_pointer {n : ℕ} (parent : External n → Option (External n))
    (name : External n → External n → MembershipPointer.Ticket) (records : List (External n)) (state : State n) :
    (WinnerCredit.run state (install parent name records)).ticket = fun record =>
      if record ∈ records then match parent record with
        | none => state.ticket record
        | some owner => name record owner
      else state.ticket record := by
  induction records generalizing state with
  | nil => simp [install, WinnerCredit.run]
  | cons record rest ih =>
      cases relation : parent record with
      | none =>
          simp only [install, relation, List.nil_append, ih]
          funext key
          by_cases same : key = record <;> by_cases member : key ∈ rest <;> simp [same, member, relation]
      | some owner =>
          simp only [install, relation, List.singleton_append, WinnerCredit.run, ih]
          funext key
          by_cases same : key = record <;> by_cases member : key ∈ rest <;>
            simp [WinnerCredit.step, same, member, relation]

def initialName {n : ℕ} (record owner : External n) : MembershipPointer.Ticket :=
  let side := decide (record.val < owner.val)
  (GreedyMerge.InitialBlocks.slot owner side, GreedyMerge.InitialBlocks.ticket owner side record)

noncomputable def initial {n : ℕ} (comparator tree : BST 0 n) : List (Action n) :=
  install (canonicalParent (Snapshot.ofTree comparator) tree) initialName Finset.univ.toList

theorem initial_erases {n : ℕ} (comparator tree : BST 0 n) :
    erase (initial comparator tree) = InitialJournal.program comparator tree := install_erases ..

theorem initial_administrative {n : ℕ} (comparator tree : BST 0 n) :
    Administrative (initial comparator tree) := install_administrative _ _ _

theorem initial_pointer {n : ℕ} (comparator tree : BST 0 n) (K : ℤ) (state : State n) :
    MembershipPointer.Synced (WinnerCredit.run state (initial comparator tree)).ticket
      (GreedyMerge.InitialBlocks.state (Snapshot.ofTree comparator) tree K) := by
  intro owner side item family member record key
  simp only [GreedyMerge.InitialBlocks.state, MembershipStamps.tagged, List.flatMap_nil, List.nil_append,
    Option.toList_some, List.flatMap_cons, List.map_map, List.append_nil, List.mem_map] at member
  obtain ⟨original, child, equal⟩ := member
  have itemEq := congrArg Prod.fst equal
  have familyEq := congrArg Prod.snd equal
  dsimp only [Function.comp_def, Prod.fst, Prod.snd] at itemEq familyEq
  subst item
  have same : record = original := Fin.ext key
  subst record
  obtain ⟨parent, onSide⟩ := (GreedyMerge.InitialBlocks.mem_children ..).mp child
  have direction : decide (original.val < owner.val) = side := by
    cases side with
    | true => simp only [GreedyMerge.InitialBlocks.sideKey, if_true] at onSide; simp [onSide]
    | false =>
        simp only [GreedyMerge.InitialBlocks.sideKey, Bool.false_eq_true, if_false] at onSide
        have less : ¬ original.val < owner.val := by omega
        simp [less]
  rw [initial, install_pointer]
  simp only [Finset.mem_toList, Finset.mem_univ, if_true, parent, initialName, direction]
  exact Prod.ext familyEq rfl

end Greedy.TicketJournal

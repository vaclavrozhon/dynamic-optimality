import MultiSplay.ForestProgram
import MultiSplay.ForestPotential

/-!
# Chronological compilation with persistent component histories

`Primitives` records concrete local realizations, including their actual event
words and output states. The compiler chooses these realizations successively.
It preserves all unselected components, carries histories across splits and
joins, and charges the initial global potential only once.
-/

namespace MultiSplay.ForestCompiler

open DynamicOptimality (RawTree)
open ChaCha.MTR.Tree (inorder size)
open ChaCha.Paper20261030.Auxiliary (Rearranges)
open CommonForest (RootAccess RotationPreparation)

variable {α σ : Type*}

abbrev PhysicalTrace := @CommonForest.Trace α RootAccess Rearranges

structure Primitives (capacity constant : Nat) (source actual : σ → RawTree α) (potential : σ → Nat) : Prop where
  rotate : ∀ (state : σ) {target : RawTree α} {depth : Nat}, Rotation depth (source state) target →
    ∃ result cost, source result = target ∧
      PhysicalTrace [actual state] [] [actual result] cost ∧
      cost + potential result ≤ potential state + constant * (depth + 1)
  service : ∀ (state : σ) {left right : RawTree α} {key : α}, source state = .node left key right →
    ∃ result cost, source result = source state ∧
      PhysicalTrace [actual state] [.search (inorder (source state)) key] [actual result] cost ∧
      cost + potential result ≤ potential state + constant
  split : ∀ (state : σ) {left right : RawTree α} {key : α}, source state = .node left key right →
    ∃ a b cost, source a = left ∧ source b = right ∧
      PhysicalTrace [actual state] [.split (inorder left) key (inorder right)] [actual a, actual b] cost ∧
      cost + potential a + potential b ≤ potential state + constant
  join : ∀ (left right : σ) (key : α), size (source left) + size (source right) + 1 ≤ capacity →
    ∃ result cost, source result = .node (source left) key (source right) ∧
      PhysicalTrace [actual left, actual right]
        [.join (inorder (source left)) key (inorder (source right))] [actual result] cost ∧
      cost + potential result ≤ potential left + potential right + constant

structure Interface (input output : CommonForest.Preparation α) (capacity constant : Nat) (source actual : σ → RawTree α) (potential : σ → Nat) (outputAccess : CommonForest.Access α := RootAccess) : Prop where
  prepare : ∀ (state : σ) {target : RawTree α} {charge : Nat}, input (source state) target charge →
    ∃ result cost, source result = target ∧
      CommonForest.Trace outputAccess output [actual state] [] [actual result] cost ∧
      cost + potential result ≤ potential state + constant * charge
  service : ∀ (state : σ) {left right : RawTree α} {key : α}, source state = .node left key right →
    ∃ result cost, source result = source state ∧
      CommonForest.Trace outputAccess output [actual state] [.search (inorder (source state)) key] [actual result] cost ∧
      cost + potential result ≤ potential state + constant
  split : ∀ (state : σ) {left right : RawTree α} {key : α}, source state = .node left key right →
    ∃ a b cost, source a = left ∧ source b = right ∧
      CommonForest.Trace outputAccess output [actual state] [.split (inorder left) key (inorder right)] [actual a, actual b] cost ∧
      cost + potential a + potential b ≤ potential state + constant
  join : ∀ (left right : σ) (key : α), size (source left) + size (source right) + 1 ≤ capacity →
    ∃ result cost, source result = .node (source left) key (source right) ∧
      CommonForest.Trace outputAccess output [actual left, actual right]
        [.join (inorder (source left)) key (inorder (source right))] [actual result] cost ∧
      cost + potential result ≤ potential left + potential right + constant

private theorem perm_lift {β γ : Type*} (f : β → γ) {a b : List γ} (order : a.Perm b)
    (initial : List β) (same : initial.map f = a) :
    ∃ final : List β, final.map f = b ∧ initial.Perm final := by
  induction order generalizing initial with
  | nil =>
      have empty := List.eq_nil_of_map_eq_nil same
      subst initial
      exact ⟨[], rfl, .nil⟩
  | cons key order ih =>
      obtain ⟨head, tail, rfl, headEq, tailEq⟩ := List.map_eq_cons_iff.mp same
      obtain ⟨final, finalEq, perm⟩ := ih tail tailEq
      exact ⟨head :: final, by simp [headEq, finalEq], perm.cons head⟩
  | swap x y rest =>
      obtain ⟨a, tail, rfl, aEq, tailEq⟩ := List.map_eq_cons_iff.mp same
      obtain ⟨b, tail, rfl, bEq, restEq⟩ := List.map_eq_cons_iff.mp tailEq
      exact ⟨b :: a :: tail, by simp [aEq, bEq, restEq], .swap _ _ _⟩
  | trans first second ih₁ ih₂ =>
      obtain ⟨middle, middleEq, firstPerm⟩ := ih₁ initial same
      obtain ⟨final, finalEq, secondPerm⟩ := ih₂ middle middleEq
      exact ⟨final, finalEq, firstPerm.trans secondPerm⟩

theorem interface_step {input output : CommonForest.Preparation α} {outputAccess : CommonForest.Access α} {capacity constant : Nat} {source actual : σ → RawTree α} {potential : σ → Nat}
    (primitives : Interface input output capacity constant source actual potential outputAccess)
    {a b : List (RawTree α)} {word : List (CommonForest.Event α)} {charge : Nat}
    (operation : CommonForest.Step RootAccess input a word b charge)
    (joins : ∀ event ∈ word, CommonForest.Domains.JoinFits capacity event)
    (initial : List σ) (same : initial.map source = a) :
    ∃ final : List σ, ∃ cost : Nat,
      final.map source = b ∧ CommonForest.Trace outputAccess output (initial.map actual) word (final.map actual) cost ∧
      cost + Forest.potential potential final ≤ Forest.potential potential initial + constant * charge := by
  induction operation generalizing initial with
  | search execution =>
      cases execution with
      | root left key right =>
          obtain ⟨state, rfl, sourceEq⟩ := List.map_eq_singleton_iff.mp same
          obtain ⟨result, cost, resultEq, run, bound⟩ := primitives.service state sourceEq
          exact ⟨[result], cost, by simp [resultEq, sourceEq], by simpa [sourceEq] using run,
            by simpa [Forest.potential] using bound⟩
  | split execution =>
      cases execution with
      | root left key right =>
          obtain ⟨state, rfl, sourceEq⟩ := List.map_eq_singleton_iff.mp same
          obtain ⟨a, b, cost, aEq, bEq, run, bound⟩ := primitives.split state sourceEq
          exact ⟨[a, b], cost, by simp [aEq, bEq], run,
            by simpa [Forest.potential, Nat.add_assoc] using bound⟩
  | join left right key =>
      obtain ⟨a, rest, rfl, aEq, restEq⟩ := List.map_eq_cons_iff.mp same
      obtain ⟨b, rfl, bEq⟩ := List.map_eq_singleton_iff.mp restEq
      have fits := joins (.join (inorder left) key (inorder right)) (by simp)
      have sizeBound : size (source a) + size (source b) + 1 ≤ capacity := by
        simpa [CommonForest.Domains.JoinFits, aEq, bEq,
          ChaCha.MTR.Tree.length_inorder, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using fits
      obtain ⟨result, cost, resultEq, run, bound⟩ := primitives.join a b key sizeBound
      exact ⟨[result], cost, by simp [resultEq, aEq, bEq], by simpa [aEq, bEq] using run,
        by simpa [Forest.potential, Nat.add_assoc] using bound⟩
  | prepare execution =>
      obtain ⟨state, rfl, sourceEq⟩ := List.map_eq_singleton_iff.mp same
      obtain ⟨result, cost, resultEq, run, bound⟩ := primitives.prepare state (sourceEq ▸ execution)
      exact ⟨[result], cost, by simp [resultEq], run, by simpa [Forest.potential] using bound⟩
  | @context a b word work operation front back ih =>
      obtain ⟨frontAndSelected, keptBack, rfl, firstEq, backEq⟩ := List.map_eq_append_iff.mp same
      obtain ⟨keptFront, selected, rfl, frontEq, selectedEq⟩ := List.map_eq_append_iff.mp firstEq
      obtain ⟨final, cost, finalEq, run, bound⟩ := ih joins selected selectedEq
      refine ⟨keptFront ++ final ++ keptBack, cost, ?_, ?_, ?_⟩
      · simp [frontEq, finalEq, backEq]
      · simpa using run.context (keptFront.map actual) (keptBack.map actual)
      · simp only [Forest.potential_append]
        omega
  | reorder order =>
      obtain ⟨final, finalEq, perm⟩ := perm_lift source order initial same
      exact ⟨final, 0, finalEq, CommonForest.Trace.single (.reorder (perm.map actual)), by
        rw [Forest.potential_perm potential perm]
        simp⟩

theorem interface_trace {input output : CommonForest.Preparation α} {outputAccess : CommonForest.Access α} {capacity constant : Nat} {source actual : σ → RawTree α} {potential : σ → Nat}
    (primitives : Interface input output capacity constant source actual potential outputAccess)
    {a b : List (RawTree α)} {word : List (CommonForest.Event α)} {charge : Nat}
    (program : CommonForest.Trace RootAccess input a word b charge)
    (joins : ∀ event ∈ word, CommonForest.Domains.JoinFits capacity event)
    (initial : List σ) (same : initial.map source = a) :
    ∃ final : List σ, ∃ cost : Nat,
      final.map source = b ∧ CommonForest.Trace outputAccess output (initial.map actual) word (final.map actual) cost ∧
      cost + Forest.potential potential final ≤ Forest.potential potential initial + constant * charge := by
  induction program generalizing initial with
  | nil => exact ⟨initial, 0, same, .nil _, by simp⟩
  | cons operation rest ih =>
      obtain ⟨middle, headCost, middleEq, headRun, headBound⟩ := interface_step primitives operation
        (fun event member => joins event (List.mem_append_left _ member)) initial same
      obtain ⟨final, tailCost, finalEq, tailRun, tailBound⟩ := ih
        (fun event member => joins event (List.mem_append_right _ member)) middle middleEq
      exact ⟨final, headCost + tailCost, finalEq, headRun.append tailRun, by
        rw [Nat.mul_add]
        omega⟩


/-- The original rotation interface is a special case of the relational compiler. -/
theorem Primitives.toInterface {capacity constant : Nat} {source actual : σ → RawTree α} {potential : σ → Nat}
    (primitives : Primitives capacity constant source actual potential) :
    Interface RotationPreparation Rearranges capacity constant source actual potential where
  prepare state {target} {charge} execution := by
    obtain ⟨depth, rotation, rfl⟩ := execution
    exact primitives.rotate state rotation
  service := primitives.service
  split := primitives.split
  join := primitives.join

theorem step {capacity constant : Nat} {source actual : σ → RawTree α} {potential : σ → Nat}
    (primitives : Primitives capacity constant source actual potential)
    {a b : List (RawTree α)} {word : List (CommonForest.Event α)} {charge : Nat}
    (operation : CommonForest.Step RootAccess RotationPreparation a word b charge)
    (joins : ∀ event ∈ word, CommonForest.Domains.JoinFits capacity event)
    (initial : List σ) (same : initial.map source = a) :
    ∃ final : List σ, ∃ cost : Nat,
      final.map source = b ∧ PhysicalTrace (initial.map actual) word (final.map actual) cost ∧
      cost + Forest.potential potential final ≤ Forest.potential potential initial + constant * charge :=
  interface_step primitives.toInterface operation joins initial same

theorem trace {capacity constant : Nat} {source actual : σ → RawTree α} {potential : σ → Nat}
    (primitives : Primitives capacity constant source actual potential)
    {a b : List (RawTree α)} {word : List (CommonForest.Event α)} {charge : Nat}
    (program : CommonForest.Program a word b charge)
    (joins : ∀ event ∈ word, CommonForest.Domains.JoinFits capacity event)
    (initial : List σ) (same : initial.map source = a) :
    ∃ final : List σ, ∃ cost : Nat,
      final.map source = b ∧ PhysicalTrace (initial.map actual) word (final.map actual) cost ∧
      cost + Forest.potential potential final ≤ Forest.potential potential initial + constant * charge :=
  interface_trace primitives.toInterface program joins initial same

end MultiSplay.ForestCompiler

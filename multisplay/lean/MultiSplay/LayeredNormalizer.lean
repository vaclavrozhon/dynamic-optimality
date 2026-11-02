import MultiSplay.SparseInitialization
import MultiSplay.RibPathSimulation

/-!
# Persistent heavy and rib layers on the same sparse component

The rib source is the actual tree of the heavy layer. A supported heavy update
is replayed through the existing rib history, using `Rib.simulate_supported`.
The combined potential pays for the first layer's work at the exact coefficient
needed by the second layer. Both histories survive ordinal reindexing.
-/

namespace MultiSplay.Layered

open Splay.Tree (BST)
open Splay.Accounting.OfflineConnectedSupport (HeavyRepresentation RibRepresentation)
open DynamicOptimality (RawTree)
open ChaCha.MTR.Tree (inorder)
open ChaCha.Paper20261030.Auxiliary (Rearranges)

structure Component (capacity : Nat) where
  lower : Nat
  upper : Nat
  source : BST lower upper
  heavy : BST lower upper
  actual : BST lower upper
  heavyRep : HeavyRepresentation capacity source heavy
  side : Bool
  ribRep : RibRepresentation capacity side heavy actual
  fits : source.size ≤ capacity

def Component.potential {capacity : Nat} (component : Component capacity) : Nat :=
  21552 * component.heavyRep.potential + component.ribRep.potential

def Component.size {capacity : Nat} (component : Component capacity) : Nat := component.source.size

theorem Component.heavyFits {capacity : Nat} (component : Component capacity) : component.heavy.size ≤ capacity :=
  (Rib.same_interval_size component.source component.heavy) ▸ component.fits

theorem Component.potential_le_size {capacity : Nat} (component : Component capacity) :
    component.potential ≤ 1379584 * component.size := by
  have heavyBound := component.heavyRep.potential_le_size
  have ribBound := component.ribRep.potential_le_size
  have same := Rib.same_interval_size component.source component.heavy
  dsimp [Component.potential, Component.size]
  omega

theorem Component.height_le {capacity : Nat} (component : Component capacity) :
    component.actual.height ≤ 30 * (Nat.clog 2 (capacity + 1)) ^ 3 := by
  have heavyBound := component.heavyRep.height_le_capacity component.fits
  have ribBound := component.ribRep.height_le component.heavyFits
  calc
    _ ≤ component.heavy.height * (5 * Nat.clog 2 (capacity + 1)) := ribBound
    _ ≤ (6 * Nat.clog 2 (capacity + 1) ^ 2) * (5 * Nat.clog 2 (capacity + 1)) :=
      Nat.mul_le_mul_right _ heavyBound
    _ = _ := by ring

structure State (capacity : Nat) (α : Type*) where
  component : Component capacity
  alphabet : Nat → α

variable {α : Type*}

def State.source {capacity : Nat} (state : State capacity α) : RawTree α :=
  Auxiliary.map state.alphabet (DynamicOptimality.BST.toRaw state.component.source)

def State.actual {capacity : Nat} (state : State capacity α) : RawTree α :=
  Auxiliary.map state.alphabet (DynamicOptimality.BST.toRaw state.component.actual)

def State.potential {capacity : Nat} (state : State capacity α) : Nat := state.component.potential

def State.size {capacity : Nat} (state : State capacity α) : Nat := state.component.size

noncomputable def State.shift {capacity : Nat} (offset : Nat) (state : State capacity α) : State capacity α where
  component := {
    lower := offset + state.component.lower
    upper := offset + state.component.upper
    source := OrdinalShift.tree offset state.component.source
    heavy := OrdinalShift.tree offset state.component.heavy
    actual := OrdinalShift.tree offset state.component.actual
    heavyRep := (OrdinalShift.heavy offset state.component.heavyRep).val
    side := state.component.side
    ribRep := (OrdinalShift.rib offset state.component.ribRep).val
    fits := by simpa using state.component.fits }
  alphabet := fun key => state.alphabet (key - offset)

@[simp] theorem State.shift_source {capacity : Nat} (offset : Nat) (state : State capacity α) :
    (state.shift offset).source = state.source := OrdinalShift.tree_alphabet _ _ _

@[simp] theorem State.shift_actual {capacity : Nat} (offset : Nat) (state : State capacity α) :
    (state.shift offset).actual = state.actual := OrdinalShift.tree_alphabet _ _ _

@[simp] theorem State.shift_size {capacity : Nat} (offset : Nat) (state : State capacity α) :
    (state.shift offset).size = state.size := OrdinalShift.tree_size _ _

@[simp] theorem State.shift_potential {capacity : Nat} (offset : Nat) (state : State capacity α) :
    (state.shift offset).potential = state.potential := by
  change 21552 * (OrdinalShift.heavy offset state.component.heavyRep).val.potential +
      (OrdinalShift.rib offset state.component.ribRep).val.potential = _
  rw [(OrdinalShift.heavy _ _).property, (OrdinalShift.rib _ _).property]
  rfl

theorem State.inorder_eq {capacity : Nat} (state : State capacity α) :
    inorder state.actual = inorder state.source := Alphabet.indexed_inorder_eq _ _ _

@[simp] theorem State.source_size {capacity : Nat} (state : State capacity α) :
    ChaCha.MTR.Tree.size state.source = state.size := by
  simp [State.source, State.size, Component.size, DynamicOptimality.BST.toRaw_size]

theorem State.potential_le_size {capacity : Nat} (state : State capacity α) :
    state.potential ≤ 1379584 * state.size := state.component.potential_le_size

/-- Simulate a source rotation through both existing layers. -/
theorem rotate_exists {capacity depth : Nat} (state : State capacity α) {target : RawTree α}
    (rotation : Rotation depth state.source target) :
    ∃ result : State capacity α, ∃ work : Nat,
      result.source = target ∧ Rearranges state.actual result.actual (18 * work) ∧
      work + result.potential ≤ state.potential + 10000128 * (depth + 1) := by
  obtain ⟨targetTree, indexed, same⟩ := rotation.lift state.component.source state.alphabet rfl
  obtain ⟨heavy⟩ := Heavy.exists_rotation indexed state.component.heavyRep state.component.fits
  obtain ⟨actual, ribRep, work, run, ribBound⟩ :=
    Rib.simulate_supported heavy.path state.component.ribRep state.component.heavyFits
  let component : Component capacity := {
    lower := state.component.lower
    upper := state.component.upper
    source := targetTree
    heavy := heavy.final
    actual := actual
    heavyRep := heavy.finalRep
    side := state.component.side
    ribRep := ribRep
    fits := indexed.size_eq ▸ state.component.fits }
  refine ⟨⟨component, state.alphabet⟩, work, same, Alphabet.rearranges state.alphabet run, ?_⟩
  have heavyBound := heavy.amortized
  change work + (21552 * heavy.finalRep.potential + ribRep.potential) ≤
    (21552 * state.component.heavyRep.potential + state.component.ribRep.potential) + 10000128 * (depth + 1)
  omega

/-- A common split first exposes the pivot through both layers and then
returns the actual pair of heavy/rib histories of each surviving child. -/
theorem split_exists {capacity : Nat} (state : State capacity α)
    {left right : RawTree α} {key : α} (root : state.source = .node left key right) :
    ∃ a b : State capacity α, ∃ work : Nat,
      a.source = left ∧ b.source = right ∧
      Rearranges state.actual (.node a.actual key b.actual) (18 * work) ∧
      work + a.potential + b.potential ≤ state.potential + 2478928 := by
  rcases state with ⟨⟨lower, upper, source, heavyTree, actual, heavyRep, side, ribRep, fits⟩, alphabet⟩
  cases source with
  | empty => simp [State.source, DynamicOptimality.BST.toRaw, Auxiliary.map] at root
  | node l r =>
      simp only [State.source, DynamicOptimality.BST.toRaw, Auxiliary.map,
        ChaCha.MTR.Tree.node.injEq] at root
      obtain ⟨heavy⟩ := Heavy.exists_split heavyRep
      have heavyFits : heavyTree.size ≤ capacity := (Rib.same_interval_size (.node l r) heavyTree) ▸ fits
      obtain ⟨exposed, exposedRep, work, run, simulatedBound⟩ :=
        Rib.simulate_supported heavy.path ribRep heavyFits
      obtain ⟨rib⟩ := Rib.exists_split exposedRep
      have leftFits : l.size ≤ capacity := by simp only [BST.size] at fits; omega
      have rightFits : r.size ≤ capacity := by simp only [BST.size] at fits; omega
      let a : State capacity α := ⟨⟨_, _, l, heavy.actualLeft, rib.actualLeft,
        heavy.leftRep, true, rib.leftRep, leftFits⟩, alphabet⟩
      let b : State capacity α := ⟨⟨_, _, r, heavy.actualRight, rib.actualRight,
        heavy.rightRep, false, rib.rightRep, rightFits⟩, alphabet⟩
      refine ⟨a, b, work + rib.work, root.1, root.2.2, ?_, ?_⟩
      · have physical := Alphabet.rearranges alphabet (run.trans (supported_rearranges rib.path))
        simpa only [a, b, State.actual, DynamicOptimality.BST.toRaw, Auxiliary.map, root.2.1, Nat.mul_add] using physical
      · have heavyBound := heavy.amortized
        have ribBound := rib.amortized
        change work + rib.work + (21552 * heavy.leftRep.potential + rib.leftRep.potential) +
          (21552 * heavy.rightRep.potential + rib.rightRep.potential) ≤
          (21552 * heavyRep.potential + ribRep.potential) + 2478928
        omega

end MultiSplay.Layered

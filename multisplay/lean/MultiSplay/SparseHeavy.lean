import MultiSplay.RepresentationShift
import MultiSplay.Alphabet
import MultiSplay.HeavyRootOperations
import MultiSplay.CommonForest
import MultiSplay.RawRotation

/-!
# Heavy normalization on sparse, changing component domains

A component keeps its persistent representation and a separate interpretation of
ordinal keys. `join_exists` accepts arbitrary local ordinal origins. It shifts
the two histories into adjacent intervals without physical work and then invokes
the proved root join. Its pointer trace starts with the literal common raw join.
-/

namespace MultiSplay.SparseHeavy

open DynamicOptimality (RawTree)
open Splay.Tree (BST)
open TangoSquared.MTR.Tree (inorder)
open TangoSquared.Paper20261030.Auxiliary (Rearranges)

variable {α : Type*}

structure State (capacity : Nat) (α : Type*) where
  component : Heavy.Component capacity
  alphabet : Nat → α

def State.source {capacity : Nat} (state : State capacity α) : RawTree α :=
  Auxiliary.map state.alphabet (DynamicOptimality.BST.toRaw state.component.source)

def State.actual {capacity : Nat} (state : State capacity α) : RawTree α :=
  Auxiliary.map state.alphabet (DynamicOptimality.BST.toRaw state.component.actual)

def State.potential {capacity : Nat} (state : State capacity α) : Nat := state.component.potential

def State.size {capacity : Nat} (state : State capacity α) : Nat := state.component.size

noncomputable def State.shift {capacity : Nat} (offset : Nat) (state : State capacity α) : State capacity α where
  component := .ofRepresentation (OrdinalShift.heavy offset state.component.representation).val
    (by simpa using state.component.fits)
  alphabet := fun key => state.alphabet (key - offset)

@[simp] theorem State.shift_source {capacity : Nat} (offset : Nat) (state : State capacity α) :
    (state.shift offset).source = state.source := OrdinalShift.tree_alphabet _ _ _

@[simp] theorem State.shift_actual {capacity : Nat} (offset : Nat) (state : State capacity α) :
    (state.shift offset).actual = state.actual := OrdinalShift.tree_alphabet _ _ _

@[simp] theorem State.shift_potential {capacity : Nat} (offset : Nat) (state : State capacity α) :
    (state.shift offset).potential = state.potential := (OrdinalShift.heavy _ _).property

@[simp] theorem State.shift_size {capacity : Nat} (offset : Nat) (state : State capacity α) :
    (state.shift offset).size = state.size := OrdinalShift.tree_size _ _

theorem State.potential_le_size {capacity : Nat} (state : State capacity α) :
    state.potential ≤ 64 * state.size := state.component.potential_le_size

theorem State.inorder_eq {capacity : Nat} (state : State capacity α) :
    inorder state.actual = inorder state.source :=
  Alphabet.indexed_inorder_eq _ _ _

@[simp] theorem State.source_size {capacity : Nat} (state : State capacity α) :
    TangoSquared.MTR.Tree.size state.source = state.size := by
  simp [State.source, State.size, Heavy.Component.size, DynamicOptimality.BST.toRaw_size]

/-- Expose the source root, returning the actual surviving child histories. -/
theorem split_exists {capacity : Nat} (state : State capacity α)
    {left right : RawTree α} {key : α} (root : state.source = .node left key right) :
    ∃ a b : State capacity α, ∃ work : Nat,
      a.source = left ∧ b.source = right ∧
      Rearranges state.actual (.node a.actual key b.actual) (18 * work) ∧
      work + a.potential + b.potential ≤ state.potential + 115 ∧
      a.size + b.size + 1 = state.size := by
  rcases state with ⟨⟨lower, upper, source, actual, representation, fits⟩, alphabet⟩
  cases source with
  | empty => simp [State.source, DynamicOptimality.BST.toRaw, Auxiliary.map] at root
  | node l r =>
      simp only [State.source, DynamicOptimality.BST.toRaw, Auxiliary.map,
        TangoSquared.MTR.Tree.node.injEq] at root
      obtain ⟨split⟩ := Heavy.exists_split representation
      have leftFits : l.size ≤ capacity := by simp only [BST.size] at fits; omega
      have rightFits : r.size ≤ capacity := by simp only [BST.size] at fits; omega
      let a : State capacity α := ⟨.ofRepresentation split.leftRep leftFits, alphabet⟩
      let b : State capacity α := ⟨.ofRepresentation split.rightRep rightFits, alphabet⟩
      refine ⟨a, b, split.work, root.1, root.2.2, ?_, split.amortized, ?_⟩
      · have path := Alphabet.rearranges alphabet (supported_rearranges split.path)
        simpa only [a, b, State.actual, Heavy.Component.ofRepresentation,
          DynamicOptimality.BST.toRaw, Auxiliary.map, root.2.1] using path
      · simp [a, b, State.size, Heavy.Component.ofRepresentation, Heavy.Component.size,
          BST.size, Nat.add_assoc, Nat.add_comm]

/-- A physical source rotation is lifted through the current alphabet. -/
theorem rotate_exists {capacity depth : Nat} (state : State capacity α) {target : RawTree α}
    (rotation : Rotation depth state.source target) :
    ∃ result : State capacity α, ∃ work : Nat,
      result.source = target ∧ Rearranges state.actual result.actual (18 * work) ∧
      work + result.potential ≤ state.potential + 464 * (depth + 1) ∧
      result.size = state.size := by
  obtain ⟨targetTree, indexed, same⟩ := rotation.lift state.component.source state.alphabet rfl
  obtain ⟨rotated⟩ := Heavy.exists_rotation indexed state.component.representation state.component.fits
  have fits : targetTree.size ≤ capacity := indexed.size_eq ▸ state.component.fits
  let result : State capacity α := ⟨.ofRepresentation rotated.finalRep fits, state.alphabet⟩
  exact ⟨result, rotated.work, same,
    Alphabet.rearranges state.alphabet (supported_rearranges rotated.path), rotated.amortized,
    indexed.size_eq.symm⟩

private theorem join_aligned {capacity : Nat} (left right : State capacity α) (key : α)
    (adjacent : left.component.upper + 1 = right.component.lower)
    (fits : left.size + right.size + 1 ≤ capacity) :
    ∃ result : State capacity α, ∃ work : Nat,
      result.source = .node left.source key right.source ∧
      Rearranges (.node left.actual key right.actual) result.actual (18 * work) ∧
      work + result.potential ≤ left.potential + right.potential + 115 ∧
      result.size = left.size + right.size + 1 := by
  rcases left with ⟨⟨lower, pivot, left, actualLeft, leftRep, leftFits⟩, leftAlphabet⟩
  rcases right with ⟨⟨rightLower, upper, right, actualRight, rightRep, rightFits⟩, rightAlphabet⟩
  change pivot + 1 = rightLower at adjacent
  subst rightLower
  have joinedFits : (BST.node left right).size ≤ capacity := by
    simpa [State.size, Heavy.Component.size, BST.size, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using fits
  obtain ⟨joined⟩ := Heavy.exists_join leftRep rightRep joinedFits
  let alphabet := Alphabet.join pivot key leftAlphabet rightAlphabet
  let result : State capacity α := ⟨.ofRepresentation joined.representation joinedFits, alphabet⟩
  refine ⟨result, joined.work, ?_, ?_, joined.amortized, ?_⟩
  · change Auxiliary.map alphabet (DynamicOptimality.BST.toRaw (.node left right)) = _
    simp [alphabet, DynamicOptimality.BST.toRaw, Auxiliary.map, Alphabet.join_root,
      Alphabet.join_left, Alphabet.join_right, State.source]
  · have path := Alphabet.rearranges alphabet (supported_rearranges joined.path)
    simpa only [alphabet, result, State.actual, Heavy.Component.ofRepresentation,
      DynamicOptimality.BST.toRaw, Auxiliary.map, Alphabet.join_root,
      Alphabet.join_left, Alphabet.join_right] using path
  · simp [result, State.size, Heavy.Component.size, Heavy.Component.ofRepresentation, BST.size,
      Nat.add_assoc, Nat.add_comm]

/-- No equality or overlap assumption on the children's ordinal intervals is
required. Their old representations and potentials are transported intact. -/
theorem join_exists {capacity : Nat} (left right : State capacity α) (key : α)
    (fits : left.size + right.size + 1 ≤ capacity) :
    ∃ result : State capacity α, ∃ work : Nat,
      result.source = .node left.source key right.source ∧
      Rearranges (.node left.actual key right.actual) result.actual (18 * work) ∧
      work + result.potential ≤ left.potential + right.potential + 115 ∧
      result.size = left.size + right.size + 1 := by
  let shiftedLeft := left.shift right.component.lower
  let shiftedRight := right.shift (left.component.upper + 1)
  have adjacent : shiftedLeft.component.upper + 1 = shiftedRight.component.lower := by
    dsimp [shiftedLeft, shiftedRight, State.shift, Heavy.Component.ofRepresentation]
    omega
  have shiftedFits : shiftedLeft.size + shiftedRight.size + 1 ≤ capacity := by
    simpa [shiftedLeft, shiftedRight] using fits
  simpa [shiftedLeft, shiftedRight] using join_aligned shiftedLeft shiftedRight key adjacent shiftedFits

/-- The physical forest word is exactly one join, with paid normalization
following it. The stated budget includes the common root insertion itself. -/
theorem join_trace {capacity : Nat} (left right : State capacity α) (key : α)
    (fits : left.size + right.size + 1 ≤ capacity) :
    ∃ result : State capacity α, ∃ cost : Nat,
      result.source = .node left.source key right.source ∧
      CommonForest.Trace (fun _ _ _ _ => False) Rearranges
        [left.actual, right.actual] [.join (inorder left.actual) key (inorder right.actual)]
        [result.actual] cost ∧
      cost + 18 * result.potential ≤ 18 * (left.potential + right.potential) + 2071 ∧
      result.size = left.size + right.size + 1 := by
  obtain ⟨result, work, sourceEq, path, bound, sizeEq⟩ := join_exists left right key fits
  refine ⟨result, 1 + 18 * work, sourceEq, ?_, by omega, sizeEq⟩
  simpa using (CommonForest.Trace.single (CommonForest.Step.join left.actual right.actual key)).append
    (CommonForest.Trace.single (CommonForest.Step.prepare path))

end MultiSplay.SparseHeavy

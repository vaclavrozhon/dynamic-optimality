import MultiSplay.RepresentationShift
import MultiSplay.Alphabet
import MultiSplay.RibRootOperations
import MultiSplay.CommonForest
import MultiSplay.RawRotation

/-!
# Rib normalization on sparse, changing component domains

Both child orientations are accepted at a join. Their paid reorientation is
performed before inserting the common root. Shifting ordinal origins preserves
all four virtual folded-stack histories and their potentials.
-/

namespace MultiSplay.SparseRib

open DynamicOptimality (RawTree)
open Splay.Tree (BST)
open TangoSquared.MTR.Tree (inorder)
open TangoSquared.Paper20261030.Auxiliary (Rearranges)

variable {α : Type*}

structure State (capacity : Nat) (α : Type*) where
  component : Rib.Component capacity
  alphabet : Nat → α

def State.source {capacity : Nat} (state : State capacity α) : RawTree α :=
  Auxiliary.map state.alphabet (DynamicOptimality.BST.toRaw state.component.source)

def State.actual {capacity : Nat} (state : State capacity α) : RawTree α :=
  Auxiliary.map state.alphabet (DynamicOptimality.BST.toRaw state.component.actual)

def State.potential {capacity : Nat} (state : State capacity α) : Nat := state.component.potential

def State.size {capacity : Nat} (state : State capacity α) : Nat := state.component.size

noncomputable def State.shift {capacity : Nat} (offset : Nat) (state : State capacity α) : State capacity α where
  component := .ofRepresentation (OrdinalShift.rib offset state.component.representation).val
    (by simpa using state.component.fits)
  alphabet := fun key => state.alphabet (key - offset)

@[simp] theorem State.shift_source {capacity : Nat} (offset : Nat) (state : State capacity α) :
    (state.shift offset).source = state.source := OrdinalShift.tree_alphabet _ _ _

@[simp] theorem State.shift_actual {capacity : Nat} (offset : Nat) (state : State capacity α) :
    (state.shift offset).actual = state.actual := OrdinalShift.tree_alphabet _ _ _

@[simp] theorem State.shift_potential {capacity : Nat} (offset : Nat) (state : State capacity α) :
    (state.shift offset).potential = state.potential := (OrdinalShift.rib _ _).property

@[simp] theorem State.shift_size {capacity : Nat} (offset : Nat) (state : State capacity α) :
    (state.shift offset).size = state.size := OrdinalShift.tree_size _ _

theorem State.potential_le_size {capacity : Nat} (state : State capacity α) :
    state.potential ≤ 256 * state.size := state.component.potential_le_size

theorem State.inorder_eq {capacity : Nat} (state : State capacity α) :
    inorder state.actual = inorder state.source :=
  Alphabet.indexed_inorder_eq _ _ _

@[simp] theorem State.source_size {capacity : Nat} (state : State capacity α) :
    TangoSquared.MTR.Tree.size state.source = state.size := by
  simp [State.source, State.size, Rib.Component.size, DynamicOptimality.BST.toRaw_size]

/-- Expose the source root, returning the actual surviving child histories. -/
theorem split_exists {capacity : Nat} (state : State capacity α)
    {left right : RawTree α} {key : α} (root : state.source = .node left key right) :
    ∃ a b : State capacity α, ∃ work : Nat,
      a.source = left ∧ b.source = right ∧
      Rearranges state.actual (.node a.actual key b.actual) (18 * work) ∧
      work + a.potential + b.potential ≤ state.potential + 448 ∧
      a.size + b.size + 1 = state.size := by
  rcases state with ⟨⟨lower, upper, side, source, actual, representation, fits⟩, alphabet⟩
  cases source with
  | empty => simp [State.source, DynamicOptimality.BST.toRaw, Auxiliary.map] at root
  | node l r =>
      simp only [State.source, DynamicOptimality.BST.toRaw, Auxiliary.map,
        TangoSquared.MTR.Tree.node.injEq] at root
      obtain ⟨split⟩ := Rib.exists_split representation
      have leftFits : l.size ≤ capacity := by simp only [BST.size] at fits; omega
      have rightFits : r.size ≤ capacity := by simp only [BST.size] at fits; omega
      let a : State capacity α := ⟨.ofRepresentation split.leftRep leftFits, alphabet⟩
      let b : State capacity α := ⟨.ofRepresentation split.rightRep rightFits, alphabet⟩
      refine ⟨a, b, split.work, root.1, root.2.2, ?_, split.amortized, ?_⟩
      · have path := Alphabet.rearranges alphabet (supported_rearranges split.path)
        simpa only [a, b, State.actual, Rib.Component.ofRepresentation,
          DynamicOptimality.BST.toRaw, Auxiliary.map, root.2.1] using path
      · simp [a, b, State.size, Rib.Component.ofRepresentation, Rib.Component.size,
          BST.size, Nat.add_assoc, Nat.add_comm]

/-- A physical source rotation is lifted through the current alphabet. -/
theorem rotate_exists {capacity depth : Nat} (state : State capacity α) {target : RawTree α}
    (rotation : Rotation depth state.source target) :
    ∃ result : State capacity α, ∃ work : Nat,
      result.source = target ∧ Rearranges state.actual result.actual (18 * work) ∧
      work + result.potential ≤ state.potential + 2694 * (depth + 1) ∧
      result.size = state.size := by
  obtain ⟨targetTree, indexed, same⟩ := rotation.lift state.component.source state.alphabet rfl
  obtain ⟨rotated⟩ := Rib.exists_rotation indexed state.component.representation state.component.fits
  have fits : targetTree.size ≤ capacity := indexed.size_eq ▸ state.component.fits
  let result : State capacity α := ⟨.ofRepresentation rotated.finalRep fits, state.alphabet⟩
  exact ⟨result, rotated.work, same,
    Alphabet.rearranges state.alphabet (supported_rearranges rotated.path), rotated.amortized,
    indexed.size_eq.symm⟩

private theorem join_aligned {capacity : Nat} (left right : State capacity α) (key : α)
    (adjacent : left.component.upper + 1 = right.component.lower)
    (fits : left.size + right.size + 1 ≤ capacity) :
    ∃ result : State capacity α, ∃ cost : Nat,
      result.source = .node left.source key right.source ∧
      CommonForest.Trace (fun _ _ _ _ => False) Rearranges
        [left.actual, right.actual] [.join (inorder left.actual) key (inorder right.actual)]
        [result.actual] cost ∧
      cost + 18 * result.potential ≤ 18 * (left.potential + right.potential) + 40321 ∧
      result.size = left.size + right.size + 1 := by
  rcases left with ⟨⟨lower, pivot, leftSide, left, actualLeft, leftRep, leftFits⟩, leftAlphabet⟩
  rcases right with ⟨⟨rightLower, upper, rightSide, right, actualRight, rightRep, rightFits⟩, rightAlphabet⟩
  change pivot + 1 = rightLower at adjacent
  subst rightLower
  have joinedFits : (BST.node left right).size ≤ capacity := by
    simpa [State.size, Rib.Component.size, BST.size, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using fits
  obtain ⟨joined⟩ := Rib.exists_join leftRep rightRep false joinedFits
  let alphabet := Alphabet.join pivot key leftAlphabet rightAlphabet
  let result : State capacity α := ⟨.ofRepresentation joined.representation joinedFits, alphabet⟩
  let l := Auxiliary.map leftAlphabet (DynamicOptimality.BST.toRaw actualLeft)
  let r := Auxiliary.map rightAlphabet (DynamicOptimality.BST.toRaw actualRight)
  let preparedL := Auxiliary.map leftAlphabet (DynamicOptimality.BST.toRaw joined.preparedLeft)
  let preparedR := Auxiliary.map rightAlphabet (DynamicOptimality.BST.toRaw joined.preparedRight)
  have leftPath : Rearranges l preparedL (18 * joined.leftWork) :=
    Alphabet.rearranges leftAlphabet (supported_rearranges joined.leftPath)
  have rightPath : Rearranges r preparedR (18 * joined.rightWork) :=
    Alphabet.rearranges rightAlphabet (supported_rearranges joined.rightPath)
  have joinPath : Rearranges (.node preparedL key preparedR) result.actual (18 * joined.joinWork) := by
    simpa only [alphabet, result, State.actual, Rib.Component.ofRepresentation,
      DynamicOptimality.BST.toRaw, Auxiliary.map, Alphabet.join_root,
      Alphabet.join_left, Alphabet.join_right] using
      Alphabet.rearranges alphabet (supported_rearranges joined.joinPath)
  let cost := 18 * joined.leftWork + (18 * joined.rightWork + (1 + 18 * joined.joinWork))
  refine ⟨result, cost, ?_, ?_, ?_, ?_⟩
  · change Auxiliary.map alphabet (DynamicOptimality.BST.toRaw (.node left right)) = _
    simp [alphabet, DynamicOptimality.BST.toRaw, Auxiliary.map, Alphabet.join_root,
      Alphabet.join_left, Alphabet.join_right, State.source]
  · have first := (CommonForest.Trace.single (CommonForest.Step.prepare
      (access := fun _ _ _ _ => False) leftPath)).context [] [r]
    have second := (CommonForest.Trace.single (CommonForest.Step.prepare
      (access := fun _ _ _ _ => False) rightPath)).context [preparedL] []
    have third := CommonForest.Trace.single (CommonForest.Step.join
      (access := fun _ _ _ _ => False) (prepare := Rearranges) preparedL preparedR key)
    have fourth := CommonForest.Trace.single (CommonForest.Step.prepare
      (access := fun _ _ _ _ => False) joinPath)
    have leftKeys : inorder preparedL = inorder l := Alphabet.indexed_inorder_eq _ _ _
    have rightKeys : inorder preparedR = inorder r := Alphabet.indexed_inorder_eq _ _ _
    simpa only [List.nil_append, List.append_nil, List.cons_append, leftKeys, rightKeys,
      l, r, cost, State.actual] using
      first.append (second.append (third.append fourth))
  · have bound := joined.amortized
    change cost + 18 * joined.representation.potential ≤
      18 * (leftRep.potential + rightRep.potential) + 40321
    dsimp [cost]
    omega
  · simp [result, State.size, Rib.Component.size, Rib.Component.ofRepresentation, BST.size,
      Nat.add_assoc, Nat.add_comm]

/-- Arbitrary sparse alphabets and arbitrary existing rib orientations. The
actual chronological trace includes both reorientations and the common join. -/
theorem join_trace {capacity : Nat} (left right : State capacity α) (key : α)
    (fits : left.size + right.size + 1 ≤ capacity) :
    ∃ result : State capacity α, ∃ cost : Nat,
      result.source = .node left.source key right.source ∧
      CommonForest.Trace (fun _ _ _ _ => False) Rearranges
        [left.actual, right.actual] [.join (inorder left.actual) key (inorder right.actual)]
        [result.actual] cost ∧
      cost + 18 * result.potential ≤ 18 * (left.potential + right.potential) + 40321 ∧
      result.size = left.size + right.size + 1 := by
  let shiftedLeft := left.shift right.component.lower
  let shiftedRight := right.shift (left.component.upper + 1)
  have adjacent : shiftedLeft.component.upper + 1 = shiftedRight.component.lower := by
    dsimp [shiftedLeft, shiftedRight, State.shift, Rib.Component.ofRepresentation]
    omega
  have shiftedFits : shiftedLeft.size + shiftedRight.size + 1 ≤ capacity := by
    simpa [shiftedLeft, shiftedRight] using fits
  simpa [shiftedLeft, shiftedRight] using join_aligned shiftedLeft shiftedRight key adjacent shiftedFits

end MultiSplay.SparseRib

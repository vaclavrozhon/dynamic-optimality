import MultiSplay.LayeredBoundedSplit

/-!
# A common join through both persistent layers

The two rib histories are reoriented while their components remain separate.
After the literal common join, rib normalization follows the supported heavy
join. Only the combined potential of the two old states is consumed.
-/

namespace MultiSplay.Layered.Bounded

open Splay.Tree (BST)
open Splay.Accounting.OfflineConnectedSupport (heavyHeight)
open DynamicOptimality (RawTree)
open TangoSquared.MTR.Tree (inorder)
open TangoSquared.Paper20261030.Auxiliary (Rearranges)
open CommonForest (RootAccess)

variable {α : Type*}


private theorem join_aligned {capacity : Nat} (left right : State capacity α) (key : α)
    (adjacent : left.component.upper + 1 = right.component.lower)
    (fits : left.size + right.size + 1 ≤ capacity) :
    ∃ result : State capacity α, ∃ cost : Nat,
      result.source = .node left.source key right.source ∧
      Trace capacity [left.actual, right.actual]
        [.join (inorder left.source) key (inorder right.source)] [result.actual] cost ∧
      cost + 18 * result.potential ≤ 18 * (left.potential + right.potential) + 44652961 := by
  rcases left with ⟨⟨lower, pivot, left, heavyLeft, actualLeft, leftHeavyRep, leftSide, leftRibRep, leftFits⟩, leftAlphabet⟩
  rcases right with ⟨⟨rightLower, upper, right, heavyRight, actualRight, rightHeavyRep, rightSide, rightRibRep, rightFits⟩, rightAlphabet⟩
  change pivot + 1 = rightLower at adjacent
  subst rightLower
  have sourceFits : (BST.node left right).size ≤ capacity := by
    simpa [State.size, Component.size, BST.size, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using fits
  have heavyFits : (BST.node heavyLeft heavyRight).size ≤ capacity :=
    (Rib.same_interval_size (.node left right) (.node heavyLeft heavyRight)) ▸ sourceFits
  obtain ⟨heavy⟩ := Heavy.exists_join leftHeavyRep rightHeavyRep sourceFits
  obtain ⟨rib⟩ := Rib.exists_join leftRibRep rightRibRep false heavyFits
  have leftFits' : left.size ≤ capacity := by simp only [BST.size] at sourceFits; omega
  have rightFits' : right.size ≤ capacity := by simp only [BST.size] at sourceFits; omega
  have hl := leftHeavyRep.height_le_capacity leftFits'
  have hr := rightHeavyRep.height_le_capacity rightFits'
  have hn := heavy_node_height leftHeavyRep rightHeavyRep sourceFits
  have hf := heavy.representation.height_le_capacity sourceFits
  have hw := heavy.work_le
  have hhl : heavyLeft.height ≤ heavyHeight capacity := by dsimp [heavyHeight]; omega
  have hhr : heavyRight.height ≤ heavyHeight capacity := by dsimp [heavyHeight]; omega
  have hhn : (BST.node heavyLeft heavyRight).height ≤ heavyHeight capacity := by dsimp [heavyHeight]; omega
  obtain ⟨final, finalRep, work, count, normalized, countBound, simulatedBound⟩ :=
    simulate heavy.path (by dsimp [heavyHeight]; omega) rib.representation heavyFits
  let alphabet := Alphabet.join pivot key leftAlphabet rightAlphabet
  let result : State capacity α := ⟨⟨lower, upper, .node left right, heavy.actual, final,
    heavy.representation, false, finalRep, sourceFits⟩, alphabet⟩
  let l := Auxiliary.map leftAlphabet (DynamicOptimality.BST.toRaw actualLeft)
  let r := Auxiliary.map rightAlphabet (DynamicOptimality.BST.toRaw actualRight)
  let preparedL := Auxiliary.map leftAlphabet (DynamicOptimality.BST.toRaw rib.preparedLeft)
  let preparedR := Auxiliary.map rightAlphabet (DynamicOptimality.BST.toRaw rib.preparedRight)
  have heavyLeftFits : heavyLeft.size ≤ capacity := by simp only [BST.size] at heavyFits; omega
  have heavyRightFits : heavyRight.size ≤ capacity := by simp only [BST.size] at heavyFits; omega
  have lh := (leftRibRep.height_le heavyLeftFits).trans (Nat.mul_le_mul_right _ hhl)
  have lph := (rib.preparedLeftRep.height_le heavyLeftFits).trans (Nat.mul_le_mul_right _ hhl)
  have rh := (rightRibRep.height_le heavyRightFits).trans (Nat.mul_le_mul_right _ hhr)
  have rph := (rib.preparedRightRep.height_le heavyRightFits).trans (Nat.mul_le_mul_right _ hhr)
  have rw := rib.work_le
  have leftPath : Preparation capacity l preparedL (18 * rib.leftWork) :=
    prepare leftAlphabet rib.leftPath (by omega) (by omega) (by omega)
      leftRibRep.geometry.1 rib.preparedLeftRep.geometry.1
  have rightPath : Preparation capacity r preparedR (18 * rib.rightWork) :=
    prepare rightAlphabet rib.rightPath (by omega) (by omega) (by omega)
      rightRibRep.geometry.1 rib.preparedRightRep.geometry.1
  have finalPath : Preparation capacity (.node preparedL key preparedR) result.actual (18 * rib.joinWork + 18 * work) := by
    have initialHeight := rib_node_height rib.preparedLeftRep rib.preparedRightRep heavyFits hhn
    have finalHeight := (rib.representation.height_le heavyFits).trans (Nat.mul_le_mul_right _ hhn)
    have first := prepare alphabet rib.joinPath initialHeight (by omega) (by omega)
      (rib_node_geometry rib.preparedLeftRep rib.preparedRightRep) rib.representation.geometry.1
    have path := first.trans (BoundedMacros.Preparation.segment alphabet normalized (show 3 * count ≤ 18 * work by omega))
    simpa only [alphabet, result, State.actual, DynamicOptimality.BST.toRaw, Auxiliary.map,
      Alphabet.join_root, Alphabet.join_left, Alphabet.join_right] using path
  let cost := 18 * rib.leftWork + (18 * rib.rightWork + (1 + (18 * rib.joinWork + 18 * work)))
  refine ⟨result, cost, ?_, ?_, ?_⟩
  · change Auxiliary.map alphabet (DynamicOptimality.BST.toRaw (.node left right)) = _
    simp [alphabet, DynamicOptimality.BST.toRaw, Auxiliary.map, Alphabet.join_root,
      Alphabet.join_left, Alphabet.join_right, State.source]
  · have first := (CommonForest.Trace.single (CommonForest.Step.prepare (access := Access capacity) leftPath)).context [] [r]
    have second := (CommonForest.Trace.single (CommonForest.Step.prepare (access := Access capacity) rightPath)).context [preparedL] []
    have third := CommonForest.Trace.single (CommonForest.Step.join
      (access := Access capacity) (prepare := Preparation capacity) preparedL preparedR key)
    have fourth := CommonForest.Trace.single (CommonForest.Step.prepare (access := Access capacity) finalPath)
    have leftKeys : inorder preparedL = inorder (Auxiliary.map leftAlphabet (DynamicOptimality.BST.toRaw left)) :=
      Alphabet.indexed_inorder_eq _ _ _
    have rightKeys : inorder preparedR = inorder (Auxiliary.map rightAlphabet (DynamicOptimality.BST.toRaw right)) :=
      Alphabet.indexed_inorder_eq _ _ _
    simpa only [List.nil_append, List.append_nil, List.cons_append, leftKeys, rightKeys,
      l, r, cost, State.actual, State.source] using first.append (second.append (third.append fourth))
  · have heavyBound := heavy.amortized
    have ribBound := rib.amortized
    change cost + 18 * (21552 * heavy.representation.potential + finalRep.potential) ≤
      18 * ((21552 * leftHeavyRep.potential + leftRibRep.potential) +
        (21552 * rightHeavyRep.potential + rightRibRep.potential)) + 44652961
    dsimp [cost]
    omega

/-- The exact common event is independent of both normalizer shapes and both
local ordinal origins. Every surviving representation history is retained. -/
theorem join_trace {capacity : Nat} (left right : State capacity α) (key : α)
    (fits : left.size + right.size + 1 ≤ capacity) :
    ∃ result : State capacity α, ∃ cost : Nat,
      result.source = .node left.source key right.source ∧
      Trace capacity [left.actual, right.actual]
        [.join (inorder left.source) key (inorder right.source)] [result.actual] cost ∧
      cost + 18 * result.potential ≤ 18 * (left.potential + right.potential) + 44652961 := by
  let shiftedLeft := left.shift right.component.lower
  let shiftedRight := right.shift (left.component.upper + 1)
  have adjacent : shiftedLeft.component.upper + 1 = shiftedRight.component.lower := by
    dsimp [shiftedLeft, shiftedRight, State.shift]
    omega
  have shiftedFits : shiftedLeft.size + shiftedRight.size + 1 ≤ capacity := by
    simpa [shiftedLeft, shiftedRight] using fits
  simpa [shiftedLeft, shiftedRight] using join_aligned shiftedLeft shiftedRight key adjacent shiftedFits

end MultiSplay.Layered.Bounded

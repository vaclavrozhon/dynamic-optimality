import MultiSplay.BoundarySingleton
import MultiSplay.InterfaceCommonSplit

/-!
# Constructing a split boundary from the actual current rich state

The source block IDs and the two growing pivot IDs are recovered from the
represented heap and its persistent records. Singleton structure, retirement
coverage, distinctness, and the value bounds are proved from representation.
They are not supplied as a new execution oracle.
-/

namespace MultiSplay.RichSplitBoundary

open Splay.Tree (BST)
open Splay.Rank (Snapshot)
open Splay.Lazy (State Block Element Side)
open Splay.Lazy.Canonical
open JoinIntervals (leftEmbedding rightEmbedding)

variable {l r : Nat}

theorem interface_lookup {n : Nat} (state : State n) (id : Fin state.blocks.length) :
    state.toInterface.block? id.val = some (state.blocks.get id).toInterface := by
  simp [State.toInterface, Splay.Interface.State.block?, List.getElem?_eq_getElem, List.get_eq_getElem]

theorem exists_boundary {params : Splay.Interface.Parameters}
    (left : BST 0 l) (right : BST 0 r) (sl : BST 0 l) (sr : BST 0 r) (state : State (0 + l + 1 + r))
    (represented : state.Represents params (Snapshot.ofTree (JoinRanks.tree left right)).withTruePriority (JoinRanks.tree sl sr)) :
    ∃ boundary : InterfaceForest.SplitBoundary state.toInterface,
      boundary.left = leftEmbedding l r (canonicalRoot (Snapshot.ofTree left).withTruePriority sl) ∧
      boundary.right = rightEmbedding l r (canonicalRoot (Snapshot.ofTree right).withTruePriority sr) ∧
      boundary.growingLeftBlock.creator = JoinRanks.pivot l r ∧
      boundary.growingRightBlock.creator = JoinRanks.pivot l r := by
  let x := leftEmbedding l r (canonicalRoot (Snapshot.ofTree left).withTruePriority sl)
  let y := rightEmbedding l r (canonicalRoot (Snapshot.ofTree right).withTruePriority sr)
  let pivot := JoinRanks.pivot l r
  have childrenNe : y ≠ x := (JoinIntervals.disjoint l r _ _).symm
  have leftChildren : state.view.topDown pivot .left = [x] := by
    rw [represented.view_eq]
    exact JoinRootGeometry.priority_topDown left right sl sr .left
  have rightChildren : state.view.topDown pivot .right = [y] := by
    rw [represented.view_eq]
    exact JoinRootGeometry.priority_topDown left right sl sr .right
  have leftMember : x ∈ state.view.topDown pivot .left := by rw [leftChildren]; simp
  have rightMember : y ∈ state.view.topDown pivot .right := by rw [rightChildren]; simp
  obtain ⟨leftParent, leftSide⟩ := state.view.mem_topDown_iff.mp leftMember
  obtain ⟨rightParent, rightSide⟩ := state.view.mem_topDown_iff.mp rightMember
  have leftAssigned := (represented.complete x).mpr (by rw [leftParent]; exact Option.some_ne_none _)
  have rightAssigned := (represented.complete y).mpr (by rw [rightParent]; exact Option.some_ne_none _)
  obtain ⟨leftBlock, leftBlockMem, leftIn⟩ := State.mem_allElements_iff.mp leftAssigned
  obtain ⟨rightBlock, rightBlockMem, rightIn⟩ := State.mem_allElements_iff.mp rightAssigned
  obtain ⟨sourceLeft, sourceLeftEq⟩ := List.mem_iff_get.mp leftBlockMem
  obtain ⟨sourceRight, sourceRightEq⟩ := List.mem_iff_get.mp rightBlockMem
  have leftShape := BoundarySingleton.block_singleton state represented.stable pivot x .left
    leftParent leftSide leftChildren leftBlock leftBlockMem leftIn
  have rightShape := BoundarySingleton.block_singleton state represented.stable pivot y .right
    rightParent rightSide rightChildren rightBlock rightBlockMem rightIn
  obtain ⟨growingLeft, leftGrowing, leftUnique⟩ := represented.oneGrowingPerSide pivot .left
  obtain ⟨growingRight, rightGrowing, rightUnique⟩ := represented.oneGrowingPerSide pivot .right
  have growingIdsNe : growingRight.val ≠ growingLeft.val := by
    intro same
    have eq : growingRight = growingLeft := Fin.ext same
    rw [eq] at rightGrowing
    have sides := leftGrowing.2.2.symm.trans rightGrowing.2.2
    cases sides
  have sourceIdsNe : sourceRight.val ≠ sourceLeft.val := by
    intro same
    have eq : sourceRight = sourceLeft := Fin.ext same
    have blocksEq : rightBlock = leftBlock := by rw [← sourceRightEq, eq, sourceLeftEq]
    have elementEq : y = x := by
      have listsEq := congrArg Block.elements blocksEq
      rw [rightShape.2.2, leftShape.2.2] at listsEq
      simpa using listsEq
    exact childrenNe elementEq
  have leftRetired : leftBlock.mode = .shrinking ∨ sourceLeft.val = growingLeft.val ∨ sourceLeft.val = growingRight.val := by
    cases modeEq : leftBlock.mode with
    | shrinking => exact Or.inl rfl
    | growing =>
        have fields : (state.blocks.get sourceLeft).mode = .growing ∧
            (state.blocks.get sourceLeft).owner = pivot ∧ (state.blocks.get sourceLeft).side = .left := by
          simpa only [sourceLeftEq] using ⟨modeEq, leftShape.1, leftShape.2.1⟩
        exact Or.inr (Or.inl (congrArg Fin.val (leftUnique sourceLeft fields)))
  have rightRetired : rightBlock.mode = .shrinking ∨ sourceRight.val = growingLeft.val ∨ sourceRight.val = growingRight.val := by
    cases modeEq : rightBlock.mode with
    | shrinking => exact Or.inl rfl
    | growing =>
        have fields : (state.blocks.get sourceRight).mode = .growing ∧
            (state.blocks.get sourceRight).owner = pivot ∧ (state.blocks.get sourceRight).side = .right := by
          simpa only [sourceRightEq] using ⟨modeEq, rightShape.1, rightShape.2.1⟩
        exact Or.inr (Or.inr (congrArg Fin.val (rightUnique sourceRight fields)))
  have leftGap : state.view.rawGap x = 2 := by
    rw [represented.view_eq]
    exact JoinPriority.left_root_rawGap left right sl sr
  have rightGap : state.view.rawGap y = 2 := by
    rw [represented.view_eq]
    exact JoinPriority.right_root_rawGap left right sl sr
  have leftValue := BoundarySingleton.value_le_three state represented.stable pivot x .left leftParent leftSide leftChildren leftGap
  have rightValue := BoundarySingleton.value_le_three state represented.stable pivot y .right rightParent rightSide rightChildren rightGap
  refine ⟨{
    left := x
    right := y
    childrenNe := childrenNe
    growingLeft := growingLeft.val
    growingRight := growingRight.val
    sourceLeft := sourceLeft.val
    sourceRight := sourceRight.val
    growingIdsNe := growingIdsNe
    sourceIdsNe := sourceIdsNe
    growingLeftBlock := (state.blocks.get growingLeft).toInterface
    growingRightBlock := (state.blocks.get growingRight).toInterface
    sourceLeftBlock := leftBlock.toInterface
    sourceRightBlock := rightBlock.toInterface
    growingLeftFound := interface_lookup state growingLeft
    growingRightFound := interface_lookup state growingRight
    sourceLeftFound := by simpa only [sourceLeftEq] using interface_lookup state sourceLeft
    sourceRightFound := by simpa only [sourceRightEq] using interface_lookup state sourceRight
    growingLeftMode := leftGrowing.1
    growingRightMode := rightGrowing.1
    sourceLeftSingleton := leftShape.2.2
    sourceRightSingleton := rightShape.2.2
    sourceLeftRetired := leftRetired
    sourceRightRetired := rightRetired
    leftValue := by change state.value x ≤ 3; omega
    rightValue := by change state.value y ≤ 3; omega }, rfl, rfl, ?_, ?_⟩
  · exact ((represented.valid.2 _ (List.get_mem _ growingLeft)).2.1 leftGrowing.1).symm.trans leftGrowing.2.1
  · exact ((represented.valid.2 _ (List.get_mem _ growingRight)).2.1 rightGrowing.1).symm.trans rightGrowing.2.1

end MultiSplay.RichSplitBoundary

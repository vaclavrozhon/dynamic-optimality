import DynamicOptimality.GeometricOnlineSimulation.GapInterior

/-!
# Unconditional destructive split on every present key

The selected key is either an existing deque separator or lies inside one
of its perfect blocks. Both cases use actual rotations. The smaller-side
transfer estimate and the exact block credit release pay the full cost.
-/

namespace DynamicOptimality.GeometricOnlineSimulation

open ChaCha.MTR ChaCha.MTR.Pointer SearchRotation DynamicOptimality.SingleFinger

private theorem perfect_decompose {levels : List Nat} (before after : List (RawTree Nat))
    (block : RawTree Nat) (perfect : List.Forall₂ Perfect levels (before ++ block :: after)) :
    ∃ first level last, levels = first ++ level :: last ∧
      List.Forall₂ Perfect first before ∧ Perfect level block ∧ List.Forall₂ Perfect last after := by
  induction before generalizing levels with
  | nil =>
      cases perfect with
      | cons head tail => exact ⟨[], _, _, rfl, .nil, head, tail⟩
  | cons first before ih =>
      cases perfect with
      | @cons level tree levels trees head tail =>
          obtain ⟨beforeLevels, selected, afterLevels, same, leftPerfect, blockPerfect, rightPerfect⟩ := ih tail
          exact ⟨level :: beforeLevels, selected, afterLevels, by simp only [same, List.cons_append],
            .cons head leftPerfect, blockPerfect, rightPerfect⟩

theorem Component.cut_block (component : Component) (before after : List (RawTree Nat))
    (block : RawTree Nat) (key : Nat) (member : key ∈ block.inorder)
    (word : component.queue.marked.holes = before ++ block :: after) :
    ∃ (left right : Component) (count : Nat),
      Rotations component.tree (.node left.tree key right.tree) count ∧
      count + left.credit + right.credit ≤ component.credit := by
  have perfect : List.Forall₂ Perfect component.levels (before ++ block :: after) := word ▸ component.perfect
  obtain ⟨beforeLevels, level, afterLevels, sameLevels, firstPerfect, blockPerfect, lastPerfect⟩ :=
    perfect_decompose before after block perfect
  obtain ⟨cut⟩ := blockPerfect.cut_exists key member
  obtain ⟨leftQueue, rightQueue, count, leftHoles, rightHoles, run, charge⟩ :=
    cut_gap component.queue before after cut word
  have oldMountain : Dyadic.Mountain (beforeLevels ++ level :: afterLevels) :=
    sameLevels ▸ component.mountain
  have newMountains := cut.dyadic.components oldMountain
  let left : Component := {
    queue := leftQueue
    levels := beforeLevels ++ cut.left.levels
    perfect := by rw [leftHoles]; exact List.rel_append firstPerfect cut.left.perfect
    mountain := newMountains.1 }
  let right : Component := {
    queue := rightQueue
    levels := cut.right.levels ++ afterLevels
    perfect := by rw [rightHoles]; exact List.rel_append cut.right.perfect lastPerfect
    mountain := newMountains.2 }
  have minBound : min before.length after.length ≤
      Dyadic.Cut.transfers beforeLevels afterLevels cut.left.levels cut.right.levels := by
    have firstLength := firstPerfect.length_eq
    have lastLength := lastPerfect.length_eq
    unfold Dyadic.Cut.transfers
    split
    · rw [firstLength]
      exact Nat.min_le_left _ _
    · rw [lastLength]
      exact Nat.min_le_right _ _
  have transfers := Dyadic.Cut.transfers_le
    (left := cut.left.levels) (right := cut.right.levels) oldMountain
  have leftWeight : Dyadic.weight (beforeLevels ++ cut.left.levels) = left.tree.size + 1 := left.weight_eq
  have rightWeight : Dyadic.weight (cut.right.levels ++ afterLevels) = right.tree.size + 1 := right.weight_eq
  rw [leftWeight, rightWeight] at transfers
  have expanded := cut.connecting_count
  have positive : 0 < cut.steps := by omega
  have credits : Dyadic.credit (beforeLevels ++ cut.left.levels) +
      Dyadic.credit (cut.right.levels ++ afterLevels) + cut.steps = Dyadic.credit component.levels := by
    rw [sameLevels]
    exact cut.dyadic.component_credits
  have physical : count + leftQueue.potential + rightQueue.potential ≤ component.queue.potential +
      100 * cut.steps + 40 * (Nat.log 2 (min (left.tree.size + 1) (right.tree.size + 1)) + 1) := by omega
  have paid := blockBudget_split credits physical
  have sizes : component.tree.size = left.tree.size + right.tree.size + 1 := by
    have same := rotations_size run
    change component.tree.size = left.tree.size + 1 + right.tree.size at same
    omega
  refine ⟨left, right, count, run, ?_⟩
  change count + blockBudget (beforeLevels ++ cut.left.levels) left.tree.size leftQueue.potential +
      blockBudget (cut.right.levels ++ afterLevels) right.tree.size rightQueue.potential ≤
      blockBudget component.levels component.tree.size component.queue.potential
  rw [sizes]
  exact paid

private theorem marked_member (marked : MarkedTree Nat) (key : Nat)
    (member : key ∈ marked.erase.inorder) :
    key ∈ marked.skeleton.inorder ∨ ∃ block ∈ marked.holes, key ∈ block.inorder := by
  induction marked with
  | hole tree => exact Or.inr ⟨tree, by simp [MarkedTree.holes], member⟩
  | node left pivot right ihl ihr =>
      simp only [MarkedTree.erase, Tree.inorder, List.mem_append, List.mem_singleton] at member
      rcases member with (inLeft | atRoot) | inRight
      · rcases ihl inLeft with selected | ⟨block, inHole, inside⟩
        · exact Or.inl (by simp [MarkedTree.skeleton, Tree.inorder, selected])
        · exact Or.inr ⟨block, by simp [MarkedTree.holes, inHole], inside⟩
      · subst key
        exact Or.inl (by simp [MarkedTree.skeleton, Tree.inorder])
      · rcases ihr inRight with selected | ⟨block, inHole, inside⟩
        · exact Or.inl (by simp [MarkedTree.skeleton, Tree.inorder, selected])
        · exact Or.inr ⟨block, by simp [MarkedTree.holes, inHole], inside⟩

/-- The destructive cut exists for every current component and every key
actually present in it. Both output states satisfy all representation
invariants, with their original keys and a telescoping rotation budget. -/
theorem Component.cut_exists (component : Component) (key : Nat) (member : key ∈ component.tree.inorder) :
    ∃ (left right : Component) (count : Nat),
      Rotations component.tree (.node left.tree key right.tree) count ∧
      count + left.credit + right.credit ≤ component.credit := by
  have visible : key ∈ component.queue.marked.erase.inorder := by
    rw [Queue.marked_erase]
    exact member
  rcases marked_member component.queue.marked key visible with separator | ⟨block, blockMember, inside⟩
  · rw [Queue.marked_keys] at separator
    obtain ⟨cell, cellMember, same⟩ := List.mem_map.mp separator
    rcases cell with ⟨pivot, gap⟩
    change pivot = key at same
    subst pivot
    obtain ⟨before, after, word, absent⟩ := List.eq_append_cons_of_mem cellMember
    exact component.cut_separator before after key gap word
  · obtain ⟨before, after, word, absent⟩ := List.eq_append_cons_of_mem blockMember
    exact component.cut_block before after block key inside word

end DynamicOptimality.GeometricOnlineSimulation

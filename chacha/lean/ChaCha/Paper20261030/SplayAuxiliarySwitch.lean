import ChaCha.Paper20261030.SplayAuxiliaryPotential
import MultiSplay.ClassicalSwitchExecution

/-!
# Amortization of actual preferred-path switches

The existing classical switch splays its pivot and at most two boundary
records, then rejoins the exposed fragments. Its incoming and parked trees
retain their exact shapes. The bound below concerns these actual rotations;
only component capacity and distinct separator identities are assumptions.
-/

namespace ChaCha.Paper20261030.SplayAuxiliary

open DynamicOptimality (RawTree)
open ChaCha.MTR
open MultiSplay Auxiliary ClassicalSwitch

variable {α : Type*}

private theorem size_mirror (tree : RawTree α) : (mirror tree).size = tree.size := by
  induction tree <;> simp [mirror,ChaCha.MTR.Tree.size, *] <;> omega

@[simp] theorem rank_mirror (tree : RawTree α) : rank (mirror tree) = rank tree := by
  simp only [rank, size_mirror]

@[simp] theorem potential_mirror (tree : RawTree α) : potential (mirror tree) = potential tree := by
  induction tree with
  | empty => rfl
  | node left key right ihl ihr =>
      simp only [mirror,potential,ihl,ihr]
      have same := rank_mirror (.node left key right)
      simp only [mirror] at same
      rw [same]
      omega

private theorem node_rank_le {capacity : Nat} {left right : RawTree α} {key : α}
    (bounded : (ChaCha.MTR.Tree.node left key right).size ≤ capacity) :
    rank (.node left key right) ≤ Nat.log 2 capacity := Nat.log_mono_right bounded

private theorem left_size_le {left right : RawTree α} {key : α} :
    left.size ≤ (ChaCha.MTR.Tree.node left key right).size := by simp only [ChaCha.MTR.Tree.size]; omega

private theorem right_size_le {left right : RawTree α} {key : α} :
    right.size ≤ (ChaCha.MTR.Tree.node left key right).size := by simp only [ChaCha.MTR.Tree.size]; omega

theorem left_switch_amortized {capacity : Nat} {pivot : α}
    {incoming whole after parked : RawTree α} {lower upper : Boundary α} {rotations : Nat}
    (run : LeftExecution pivot incoming lower upper whole after parked rotations)
    (unique : whole.inorder.Nodup) (bounded : whole.size ≤ capacity)
    (afterBounded : after.size ≤ capacity) :
    rotations+2*(potential after+potential parked) ≤
      2*(potential whole+potential incoming)+24*Nat.log 2 capacity+3 := by
  classical
  cases run with
  | @neither whole old work pivotSplay =>
      have first := splay_amortized_capacity pivotSplay unique bounded
      have joined := node_rank_le afterBounded
      simp only [potential] at first joined ⊢
      omega
  | @lower whole left a old lo pivotWork lowerWork pivotSplay lowerSplay =>
      have first := splay_amortized_capacity pivotSplay unique bounded
      have parts := nodup_node (pivotSplay.inorder_eq ▸ unique)
      have leftBound : left.size ≤ capacity :=
        left_size_le.trans (pivotSplay.size_eq ▸ bounded)
      have second := splay_amortized_capacity lowerSplay parts.1 leftBound
      have joined := node_rank_le afterBounded
      have lowerJoined := node_rank_le (left_size_le.trans afterBounded)
      simp only [potential] at first second joined lowerJoined ⊢
      omega
  | @upper whole old right b hi pivotWork upperWork pivotSplay upperSplay =>
      have first := splay_amortized_capacity pivotSplay unique bounded
      have parts := nodup_node (pivotSplay.inorder_eq ▸ unique)
      have rightBound : right.size ≤ capacity :=
        right_size_le.trans (pivotSplay.size_eq ▸ bounded)
      have second := splay_amortized_capacity upperSplay parts.2.1 rightBound
      have joined := node_rank_le afterBounded
      have upperJoined := node_rank_le (right_size_le.trans afterBounded)
      simp only [potential] at first second joined upperJoined ⊢
      omega
  | @both whole left right a old b lo hi pivotWork lowerWork upperWork pivotSplay lowerSplay upperSplay =>
      have first := splay_amortized_capacity pivotSplay unique bounded
      have parts := nodup_node (pivotSplay.inorder_eq ▸ unique)
      have leftBound : left.size ≤ capacity :=
        left_size_le.trans (pivotSplay.size_eq ▸ bounded)
      have rightBound : right.size ≤ capacity :=
        right_size_le.trans (pivotSplay.size_eq ▸ bounded)
      have second := splay_amortized_capacity lowerSplay parts.1 leftBound
      have third := splay_amortized_capacity upperSplay parts.2.1 rightBound
      have joined := node_rank_le afterBounded
      have lowerJoined := node_rank_le (left_size_le.trans afterBounded)
      have upperJoined := node_rank_le (right_size_le.trans afterBounded)
      simp only [potential] at first second third joined lowerJoined upperJoined ⊢
      omega

/-- A switch costs logarithmic amortized rotations, including both physical
output components in the same potential. No incoming component is reset. -/
theorem switch_amortized {capacity : Nat} {pivot : α}
    {incoming whole after parked : RawTree α} {side : Bool}
    {lower upper : Boundary α} {rotations : Nat}
    (run : Execution pivot incoming side lower upper whole after parked rotations)
    (unique : whole.inorder.Nodup) (bounded : whole.size ≤ capacity)
    (afterBounded : after.size ≤ capacity) :
    rotations+2*(potential after+potential parked) ≤
      2*(potential whole+potential incoming)+24*Nat.log 2 capacity+3 := by
  cases run with
  | left run => exact left_switch_amortized run unique bounded afterBounded
  | right run =>
      have mirroredUnique : (mirror whole).inorder.Nodup := by
        simpa only [inorder_mirror,List.nodup_reverse] using unique
      have result := left_switch_amortized run mirroredUnique
        (by simpa only [size_mirror] using bounded)
        (by simpa only [size_mirror] using afterBounded)
      simpa only [potential_mirror] using result

end ChaCha.Paper20261030.SplayAuxiliary

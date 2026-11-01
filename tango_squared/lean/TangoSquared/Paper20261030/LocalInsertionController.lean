import TangoSquared.Paper20261030.LocalJoinProgram

/-! Boundary cases of the local join controller. The separator already
exists as the current vertex. Each recursive descent rotates it past the
old root; the return phase invokes the verified local balance controller. -/

namespace TangoSquared.Paper20261030.Auxiliary.JoinController

open Std.DTreeMap.Internal Std.DTreeMap.Internal.Impl
open MTR DynamicOptimality DynamicOptimality.LocalProgram

variable {α ρ : Type*}

theorem insertMin_prefix (old : Nat) (key : α) (value : ρ)
    (tree : Impl α (fun _ => ρ)) (balanced : tree.Balanced) (depth : Nat) (outside) :
    ∃ reads cost, Steps program (.observing depth (.read 3 []))
      ⟨recordTree (.inner old key value .leaf tree),outside⟩ (.returning depth)
      ⟨recordTree (insertMin key value tree balanced).impl,outside⟩ reads cost ∧
      cost ≤ 100*height tree+44 := by
  induction tree generalizing depth outside with
  | leaf =>
    obtain ⟨cost,bound,observed⟩ := inspect depth old key value .leaf .leaf outside
    have write : Step program (.refresh depth 1) ⟨recordTree (.inner old key value .leaf .leaf),outside⟩
        (.returning depth) ⟨recordTree (bin key value .leaf .leaf),outside⟩ none := .writeSize rfl
    exact ⟨_,cost+1,observed.append write.prefix,by simp only [height]; omega⟩
  | inner size rk rv left right ihl ihr =>
    let child := insertMin key value left balanced.left
    have precondition : BalanceLPrecond child.impl.size right.size := by
      right
      rw [child.size_impl]
      exact ⟨by omega,by simpa using balanced.at_root⟩
    have target : balanceₘ rk rv child.impl right =
        (insertMin key value (.inner size rk rv left right) balanced).impl := by
      rw [insertMin]
      change _ = balanceL rk rv child.impl right child.balanced_impl balanced.right precondition
      rw [balanceL_eq_balanceLErase,balanceLErase_eq_balanceL!,
        balanceL!_eq_balance! child.balanced_impl balanced.right precondition.erase,
        balance!_eq_balanceₘ child.balanced_impl balanced.right (Or.inl precondition.erase)]
    obtain ⟨readCost,readBound,observed⟩ := inspect depth old key value .leaf (.inner size rk rv left right) outside
    obtain ⟨childReads,childCost,childRun,childBound⟩ := ihl balanced.left (depth+1)
      (.left (size,⟨rk,rv⟩) (recordTree right)::outside)
    obtain ⟨returnCost,returnBound,returned⟩ := return_left depth size rk rv child.impl right outside
    rw [target] at returned
    have turned := turn_right depth .empty (recordTree left) (recordTree right)
      (old,⟨key,value⟩) (size,⟨rk,rv⟩) outside
    refine ⟨_,readCost+2+childCost+returnCost,((observed.append turned).append childRun).append returned,?_⟩
    simp only [height]
    have := Nat.le_max_left (height left) (height right)
    omega

theorem insertMax_prefix (old : Nat) (key : α) (value : ρ)
    (tree : Impl α (fun _ => ρ)) (balanced : tree.Balanced) (depth : Nat) (outside) :
    ∃ reads cost, Steps program (.observing depth (.read 3 []))
      ⟨recordTree (.inner old key value tree .leaf),outside⟩ (.returning depth)
      ⟨recordTree (insertMax key value tree balanced).impl,outside⟩ reads cost ∧
      cost ≤ 100*height tree+44 := by
  induction tree generalizing depth outside with
  | leaf =>
    obtain ⟨cost,bound,observed⟩ := inspect depth old key value .leaf .leaf outside
    have write : Step program (.refresh depth 1) ⟨recordTree (.inner old key value .leaf .leaf),outside⟩
        (.returning depth) ⟨recordTree (bin key value .leaf .leaf),outside⟩ none := .writeSize rfl
    exact ⟨_,cost+1,observed.append write.prefix,by simp only [height]; omega⟩
  | inner size lk lv left right ihl ihr =>
    let child := insertMax key value right balanced.right
    have precondition : BalanceLPrecond child.impl.size left.size := by
      right
      rw [child.size_impl]
      exact ⟨by omega,by simpa using balanced.at_root.symm⟩
    have target : balanceₘ lk lv left child.impl =
        (insertMax key value (.inner size lk lv left right) balanced).impl := by
      rw [insertMax]
      change _ = balanceR lk lv left child.impl balanced.left child.balanced_impl precondition
      rw [balanceR_eq_balanceRErase,balanceRErase_eq_balanceR!,
        balanceR!_eq_balance! balanced.left child.balanced_impl precondition.erase,
        balance!_eq_balanceₘ balanced.left child.balanced_impl (Or.inr precondition.erase)]
    obtain ⟨readCost,readBound,observed⟩ := inspect depth old key value (.inner size lk lv left right) .leaf outside
    obtain ⟨childReads,childCost,childRun,childBound⟩ := ihr balanced.right (depth+1)
      (.right (recordTree left) (size,⟨lk,lv⟩)::outside)
    obtain ⟨returnCost,returnBound,returned⟩ := return_right depth size lk lv left child.impl outside
    rw [target] at returned
    have turned := turn_left depth (recordTree left) (recordTree right) .empty
      (size,⟨lk,lv⟩) (old,⟨key,value⟩) outside
    refine ⟨_,readCost+2+childCost+returnCost,((observed.append turned).append childRun).append returned,?_⟩
    simp only [height]
    have := Nat.le_max_right (height left) (height right)
    omega

end TangoSquared.Paper20261030.Auxiliary.JoinController

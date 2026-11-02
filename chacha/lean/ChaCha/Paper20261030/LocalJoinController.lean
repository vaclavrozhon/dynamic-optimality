import ChaCha.Paper20261030.LocalInsertionController
import ChaCha.Paper20261030.LocalJoinSteps

/-! Correctness and logarithmic cost of the actual local join program.
The result is the same standard-library join already used by the Cha-Cha
representation and accounting proofs. Both subtrees may be empty, and the
separator's cached size may initially be stale. -/

namespace ChaCha.Paper20261030.Auxiliary.JoinController

open Std.DTreeMap.Internal Std.DTreeMap.Internal.Impl
open MTR DynamicOptimality DynamicOptimality.LocalProgram

variable {α ρ : Type*}

theorem link_prefix_steps (old : Nat) (key : α) (value : ρ) (left right : Impl α (fun _ => ρ))
    (leftBalanced : left.Balanced) (rightBalanced : right.Balanced) (depth : Nat) (outside) :
    ∃ reads cost, Steps program (.observing depth (.read 3 []))
      ⟨recordTree (.inner old key value left right),outside⟩ (.returning depth)
      ⟨recordTree (link key value left right leftBalanced rightBalanced).impl,outside⟩ reads cost ∧
      cost ≤ 100*recursionDepth left right+44 := by
  cases left with
  | leaf =>
    simpa only [link,recursionDepth] using insertMin_prefix old key value right rightBalanced depth outside
  | inner sl lk lv ll lr =>
    cases right with
    | leaf =>
      simpa only [link,recursionDepth] using
        insertMax_prefix old key value (.inner sl lk lv ll lr) leftBalanced depth outside
    | inner sr rk rv rl rr =>
      by_cases hright : delta*sl < sr
      · let child := link key value (.inner sl lk lv ll lr) rl leftBalanced rightBalanced.left
        have precondition : BalanceLErasePrecond child.impl.size rr.size := by
          rw [child.size_impl]
          exact join_balance_precond _ _ _ _ leftBalanced.one_le rightBalanced.eq rightBalanced.at_root hright
        have target : balanceₘ rk rv child.impl rr =
            (link key value (.inner sl lk lv ll lr) (.inner sr rk rv rl rr) leftBalanced rightBalanced).impl := by
          rw [link,dif_pos hright]
          change _ = balanceLErase rk rv child.impl rr child.balanced_impl rightBalanced.right precondition
          rw [balanceLErase_eq_balanceL!,balanceL!_eq_balance! child.balanced_impl rightBalanced.right precondition,
            balance!_eq_balanceₘ child.balanced_impl rightBalanced.right (Or.inl precondition)]
        obtain ⟨readCost,readBound,observed⟩ := inspect depth old key value
          (.inner sl lk lv ll lr) (.inner sr rk rv rl rr) outside
        simp only [capture,choice,hright,ite_true,dispatch] at observed
        obtain ⟨childReads,childCost,childRun,childBound⟩ := link_prefix_steps old key value
          (.inner sl lk lv ll lr) rl leftBalanced rightBalanced.left (depth+1)
          (.left (sr,⟨rk,rv⟩) (recordTree rr)::outside)
        obtain ⟨returnCost,returnBound,returned⟩ := return_left depth sr rk rv child.impl rr outside
        rw [target] at returned
        have turned := turn_right depth (recordTree (.inner sl lk lv ll lr)) (recordTree rl) (recordTree rr)
          (old,⟨key,value⟩) (sr,⟨rk,rv⟩) outside
        refine ⟨_,readCost+2+childCost+returnCost,((observed.append turned).append childRun).append returned,?_⟩
        rw [recursionDepth,if_pos hright]
        omega
      · by_cases hleft : delta*sr < sl
        · let child := link key value lr (.inner sr rk rv rl rr) leftBalanced.right rightBalanced
          have precondition : BalanceLErasePrecond child.impl.size ll.size := by
            rw [child.size_impl]
            have size : sl = lr.size+1+ll.size := by have := leftBalanced.eq; omega
            have bound := join_balance_precond _ _ _ _ rightBalanced.one_le size leftBalanced.at_root.symm hleft
            simpa [Impl.size_inner,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using bound
          have target : balanceₘ lk lv ll child.impl =
              (link key value (.inner sl lk lv ll lr) (.inner sr rk rv rl rr) leftBalanced rightBalanced).impl := by
            rw [link,dif_neg hright,dif_pos hleft]
            change _ = balanceRErase lk lv ll child.impl leftBalanced.left child.balanced_impl precondition
            rw [balanceRErase_eq_balanceR!,balanceR!_eq_balance! leftBalanced.left child.balanced_impl precondition,
              balance!_eq_balanceₘ leftBalanced.left child.balanced_impl (Or.inr precondition)]
          obtain ⟨readCost,readBound,observed⟩ := inspect depth old key value
            (.inner sl lk lv ll lr) (.inner sr rk rv rl rr) outside
          simp only [capture,choice,hright,hleft,ite_false,ite_true,dispatch] at observed
          obtain ⟨childReads,childCost,childRun,childBound⟩ := link_prefix_steps old key value
            lr (.inner sr rk rv rl rr) leftBalanced.right rightBalanced (depth+1)
            (.right (recordTree ll) (sl,⟨lk,lv⟩)::outside)
          obtain ⟨returnCost,returnBound,returned⟩ := return_right depth sl lk lv ll child.impl outside
          rw [target] at returned
          have turned := turn_left depth (recordTree ll) (recordTree lr) (recordTree (.inner sr rk rv rl rr))
            (sl,⟨lk,lv⟩) (old,⟨key,value⟩) outside
          refine ⟨_,readCost+2+childCost+returnCost,((observed.append turned).append childRun).append returned,?_⟩
          rw [recursionDepth,if_neg hright,if_pos hleft]
          omega
        · rw [link,dif_neg hright,dif_neg hleft]
          obtain ⟨readCost,readBound,observed⟩ := inspect depth old key value
            (.inner sl lk lv ll lr) (.inner sr rk rv rl rr) outside
          simp only [capture,choice,hright,hleft,ite_false,dispatch] at observed
          have write : Step program (.refresh depth (sl+1+sr))
              ⟨recordTree (.inner old key value (.inner sl lk lv ll lr) (.inner sr rk rv rl rr)),outside⟩
              (.returning depth)
              ⟨recordTree (bin key value (.inner sl lk lv ll lr) (.inner sr rk rv rl rr)),outside⟩ none := .writeSize rfl
          exact ⟨_,readCost+1,observed.append write.prefix,by
            rw [recursionDepth,if_neg hright,if_neg hleft]; omega⟩
termination_by sizeOf left+sizeOf right

theorem link_prefix (old : Nat) (key : α) (value : ρ) (left right : Impl α (fun _ => ρ))
    (leftBalanced : left.Balanced) (rightBalanced : right.Balanced) (depth : Nat) (outside) :
    ∃ reads cost, Steps program (.observing depth (.read 3 []))
      ⟨recordTree (.inner old key value left right),outside⟩ (.returning depth)
      ⟨recordTree (link key value left right leftBalanced rightBalanced).impl,outside⟩ reads cost ∧
      cost ≤ 100*(height left+height right)+44 := by
  obtain ⟨reads,cost,run,bound⟩ := link_prefix_steps old key value left right leftBalanced rightBalanced depth outside
  have heightBound := recursionDepth_height left right
  exact ⟨reads,cost,run,by omega⟩

theorem link_prefix_right_rank (old : Nat) (key : α) (value : ρ) (left right : Impl α (fun _ => ρ))
    (leftBalanced : left.Balanced) (rightBalanced : right.Balanced) (order : left.size ≤ delta*right.size)
    (depth : Nat) (outside) :
    ∃ reads cost, Steps program (.observing depth (.read 3 []))
      ⟨recordTree (.inner old key value left right),outside⟩ (.returning depth)
      ⟨recordTree (link key value left right leftBalanced rightBalanced).impl,outside⟩ reads cost ∧
      cost+990*Nat.log 2 (left.size+1) ≤ 990*Nat.clog 2 (left.size+right.size+2)+76 := by
  obtain ⟨reads,cost,run,bound⟩ := link_prefix_steps old key value left right leftBalanced rightBalanced depth outside
  have rankBound := weight_steps_log (by omega : left.size+1 ≠ 0)
    (recursionDepth_right_weight left right leftBalanced rightBalanced order)
  exact ⟨reads,cost,run,by omega⟩

theorem link_prefix_left_rank (old : Nat) (key : α) (value : ρ) (left right : Impl α (fun _ => ρ))
    (leftBalanced : left.Balanced) (rightBalanced : right.Balanced) (order : right.size ≤ delta*left.size)
    (depth : Nat) (outside) :
    ∃ reads cost, Steps program (.observing depth (.read 3 []))
      ⟨recordTree (.inner old key value left right),outside⟩ (.returning depth)
      ⟨recordTree (link key value left right leftBalanced rightBalanced).impl,outside⟩ reads cost ∧
      cost+990*Nat.log 2 (right.size+1) ≤ 990*Nat.clog 2 (left.size+right.size+2)+76 := by
  obtain ⟨reads,cost,run,bound⟩ := link_prefix_steps old key value left right leftBalanced rightBalanced depth outside
  have rankBound := weight_steps_log (by omega : right.size+1 ≠ 0)
    (recursionDepth_left_weight left right leftBalanced rightBalanced order)
  exact ⟨reads,cost,run,by omega⟩

theorem link_run (old : Nat) (key : α) (value : ρ) (left right : Impl α (fun _ => ρ))
    (leftBalanced : left.Balanced) (rightBalanced : right.Balanced) (outside) :
    ∃ reads cost, Run program (.observing 0 (.read 3 []))
      ⟨recordTree (.inner old key value left right),outside⟩ (.returning 0)
      ⟨recordTree (link key value left right leftBalanced rightBalanced).impl,outside⟩ reads cost ∧
      cost ≤ 300*(Nat.clog 2 (left.size+1)+Nat.clog 2 (right.size+1))+44 := by
  obtain ⟨reads,cost,run,bound⟩ := link_prefix old key value left right leftBalanced rightBalanced 0 outside
  have leftHeight := balanced_height_log leftBalanced
  have rightHeight := balanced_height_log rightBalanced
  exact ⟨reads,cost,run.run rfl,by omega⟩

end ChaCha.Paper20261030.Auxiliary.JoinController

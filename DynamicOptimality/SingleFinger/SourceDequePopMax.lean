import DynamicOptimality.SingleFinger.SourceDequePop

/-! The symmetric maximum endpoint operation, with the same concrete
single-pointer execution and persistent potential as minimum removal. -/

namespace DynamicOptimality.SingleFinger.SourceDeque

open ChaCha.Paper20261030 ColoredStorage SourcePointer SourceLocalProgram
open DynamicOptimality.LocalProgram (Move)
open SourceSpine SourceCounted

variable {κ α ρ : Type*}

theorem pop_max (layout : Layout α ρ)
    (enough : 2 ≤ layout.cells.length)
    (outside : List (Frame α ρ)) (rest : Schedule) :
    ∃ (after : Layout α ρ) (entry : ρ) (gap : Source α ρ) (cost : Nat),
      layout.cells = after.cells++[(entry,gap)] ∧ after.gap = layout.gap ∧
      Steps code (popMaxPlan layout.front.length layout.back.length rest)
        ⟨layout.tree,outside⟩ rest ⟨after.tree,.left entry gap::outside⟩ [] cost ∧
      cost+after.potential ≤ layout.potential+14 ∧
      after.front.length = (if layout.back.length = 0 then
        if layout.front.length = 1 then 0 else (layout.front.length+1)/2 else layout.front.length) ∧
      after.back.length = (if layout.back.length = 0 then
        layout.front.length-(layout.front.length+1)/2-1 else layout.back.length-1) := by
  rcases layout with ⟨gap,front,pivot,afterGap,back⟩
  induction back using List.reverseRecOn with
  | append_singleton back cell ih =>
    rcases cell with ⟨entry,nextGap⟩
    refine ⟨⟨gap,front,pivot,afterGap,back⟩,entry,nextGap,2,?_,rfl,?_,?_,?_,?_⟩
    · simp only [Layout.cells,List.append_assoc,List.cons_append]
    · simpa only [popMaxPlan,List.length_append,List.length_singleton,Nat.succ_ne_zero,if_false] using
        pop_max_fast gap front pivot afterGap back entry nextGap outside rest
    · have bound := pop_max_fast_amortized front.length back.length
      simpa only [Layout.potential,List.length_append,List.length_singleton] using (by omega :
        2+potential front.length back.length ≤ potential front.length (back.length+1)+14)
    · simp
    · simp
  | nil =>
    cases front with
    | nil => simp [Layout.cells] at enough
    | cons cell front =>
      rcases cell with ⟨first,firstGap⟩
      cases front with
      | nil =>
        refine ⟨⟨gap,[],first,firstGap,[]⟩,pivot,afterGap,1,rfl,rfl,?_,?_,?_,?_⟩
        · exact SourceCounted.one rfl rest
        · simp [Layout.potential,potential]
        · simp
        · simp
      | cons cell front =>
        let old : Layout α ρ := ⟨gap,(first,firstGap)::cell::front,pivot,afterGap,[]⟩
        obtain ⟨newFront,newCell,newBack,same,frontLength,backLength⟩ :=
          middle_split old.cells (by simp [old,Layout.cells])
        rcases newCell with ⟨newPivot,newAfter⟩
        have total : old.cells.length = front.length+3 := by simp [old,Layout.cells]
        have frontPositive : 0 < newFront.length := by omega
        have backPositive : 0 < newBack.length := by omega
        have equalSize : old.front.length = newFront.length+newBack.length := by
          simp only [old,List.length_cons]
          omega
        have balanced : newFront.length ≤ newBack.length+1 ∧ newBack.length ≤ newFront.length+1 := by omega
        have rebuilt := rebuild gap old.front pivot afterGap [] newFront newPivot newAfter newBack same
          outside (popMaxFast rest)
        induction newBack using List.reverseRecOn with
        | nil => simp at backPositive
        | append_singleton back next ih =>
          rcases next with ⟨entry,nextGap⟩
          have lastRun := pop_max_fast gap newFront newPivot newAfter back entry nextGap outside rest
          have combined := rebuilt.append lastRun
          let after : Layout α ρ := ⟨gap,newFront,newPivot,newAfter,back⟩
          refine ⟨after,entry,nextGap,rebuildCost old.front.length 0 newFront.length (back.length+1)+2,
            ?_,rfl,?_,?_,?_,?_⟩
          · simpa only [old,after,Layout.cells,List.append_assoc,List.cons_append] using same
          · have countFront : newFront.length = (old.front.length+1)/2 := by
              simp only [old,List.length_cons] at ⊢
              omega
            have countBack : back.length+1 = old.front.length-(old.front.length+1)/2 := by
              simp only [List.length_append,List.length_singleton] at backLength
              simp only [old,List.length_cons] at ⊢
              omega
            simpa only [old,after,Layout.tree,popMaxPlan,List.length_nil,List.length_cons,
              List.length_append,List.length_singleton,
              Nat.succ_ne_zero,show front.length+1+1 ≠ 1 by omega,if_true,if_false,
              List.nil_append,countFront,countBack] using combined
          · have bound := depleted_max_amortized equalSize balanced backPositive
            simpa only [Layout.potential,after,old,List.length_nil,List.length_cons,
              List.length_append,List.length_singleton,Nat.add_sub_cancel] using bound
          · simp only [after,old,List.length_nil,List.length_cons,ite_true,
              if_neg (show front.length+1+1 ≠ 1 by omega)]
            omega
          · simp only [after,old,List.length_nil,List.length_cons,ite_true]
            simp only [List.length_append,List.length_singleton] at backLength
            omega

end DynamicOptimality.SingleFinger.SourceDeque

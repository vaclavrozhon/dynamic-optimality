import DynamicOptimality.SingleFinger.SourceDequeEndpoints

/-! Complete nonempty-remainder deque pops. The online schedule uses only the
current spine lengths. Its potential is retained in the resulting layout,
including across linear rebuilding when the requested side is exhausted.
The singleton case requires no rotation: its sole cell is already exposed.
-/

namespace DynamicOptimality.SingleFinger.SourceDeque

open ChaCha.Paper20261030 ColoredStorage SourcePointer SourceLocalProgram
open DynamicOptimality.LocalProgram (Move)
open SourceSpine SourceCounted

variable {κ α ρ : Type*}

def popMinPlan (front back : Nat) (rest : Schedule) : Schedule :=
  if front = 0 then
    if back = 1 then prepend .right 1 rest
    else rebuildPlan 0 back ((back+1)/2) (back-(back+1)/2) (popMinFast rest)
  else popMinFast rest

def popMaxPlan (front back : Nat) (rest : Schedule) : Schedule :=
  if back = 0 then
    if front = 1 then prepend .left 1 rest
    else rebuildPlan front 0 ((front+1)/2) (front-(front+1)/2) (popMaxFast rest)
  else popMaxFast rest

/-- Every pop from a deque of at least two cells executes legally, returns a
concrete remaining deque, and satisfies a persistent amortized bound of 14.
The popped cell is the physical parent of the returned deque cursor. -/
theorem pop_min (layout : Layout α ρ)
    (enough : 2 ≤ layout.cells.length)
    (outside : List (Frame α ρ)) (rest : Schedule) :
    ∃ (after : Layout α ρ) (entry : ρ) (cost : Nat),
      layout.cells = (entry,after.gap)::after.cells ∧
      Steps code (popMinPlan layout.front.length layout.back.length rest)
        ⟨layout.tree,outside⟩ rest ⟨after.tree,.right layout.gap entry::outside⟩ [] cost ∧
      cost+after.potential ≤ layout.potential+14 ∧
      after.front.length = (if layout.front.length = 0 then (layout.back.length+1)/2-1
        else layout.front.length-1) ∧
      after.back.length = (if layout.front.length = 0 then layout.back.length-(layout.back.length+1)/2
        else layout.back.length) := by
  rcases layout with ⟨gap,front,pivot,afterGap,back⟩
  cases front with
  | cons cell front =>
    rcases cell with ⟨entry,nextGap⟩
    refine ⟨⟨nextGap,front,pivot,afterGap,back⟩,entry,2,rfl,?_,?_,?_,?_⟩
    · simpa only [popMinPlan,List.length_cons,Nat.succ_ne_zero,if_false] using
        pop_min_fast gap entry nextGap front pivot afterGap back outside rest
    · have bound := pop_min_fast_amortized front.length back.length
      simpa only [Layout.potential,List.length_cons] using (by omega :
        2+potential front.length back.length ≤ potential (front.length+1) back.length+14)
    · simp
    · simp
  | nil =>
    cases back with
    | nil => simp [Layout.cells] at enough
    | cons cell back =>
      rcases cell with ⟨last,lastGap⟩
      cases back with
      | nil =>
        refine ⟨⟨afterGap,[],last,lastGap,[]⟩,pivot,1,rfl,?_,?_,?_,?_⟩
        · exact SourceCounted.one rfl rest
        · simp [Layout.potential,potential]
        · simp
        · simp
      | cons cell back =>
        let old : Layout α ρ := ⟨gap,[],pivot,afterGap,(last,lastGap)::cell::back⟩
        obtain ⟨newFront,newCell,newBack,same,frontLength,backLength⟩ :=
          middle_split old.cells (by simp [old,Layout.cells])
        rcases newCell with ⟨newPivot,newAfter⟩
        have total : old.cells.length = back.length+3 := by simp [old,Layout.cells]
        have frontPositive : 0 < newFront.length := by omega
        have backPositive : 0 < newBack.length := by omega
        have equalSize : old.back.length = newFront.length+newBack.length := by
          simp only [old,List.length_cons]
          omega
        have balanced : newFront.length ≤ newBack.length+1 ∧ newBack.length ≤ newFront.length+1 := by omega
        have rebuilt := rebuild gap [] pivot afterGap old.back newFront newPivot newAfter newBack same
          outside (popMinFast rest)
        cases newFront with
        | nil => simp at frontPositive
        | cons next front =>
          rcases next with ⟨entry,nextGap⟩
          have lastRun := pop_min_fast gap entry nextGap front newPivot newAfter newBack outside rest
          have combined := rebuilt.append lastRun
          let after : Layout α ρ := ⟨nextGap,front,newPivot,newAfter,newBack⟩
          refine ⟨after,entry,rebuildCost 0 old.back.length (front.length+1) newBack.length+2,?_,?_,?_,?_,?_⟩
          · exact same
          · have countFront : front.length+1 = (old.back.length+1)/2 := by
              simp only [List.length_cons] at frontLength
              simp only [old,List.length_cons] at ⊢
              omega
            have countBack : newBack.length = old.back.length-(old.back.length+1)/2 := by
              simp only [old,List.length_cons] at ⊢
              omega
            simpa only [old,after,Layout.tree,popMinPlan,List.length_nil,List.length_cons,
              Nat.succ_ne_zero,show back.length+1+1 ≠ 1 by omega,if_true,if_false,
              List.nil_append,countFront,countBack] using combined
          · have bound := depleted_min_amortized equalSize balanced frontPositive
            simpa only [Layout.potential,after,old,List.length_nil,List.length_cons,
              Nat.add_sub_cancel] using bound
          · simp only [after,List.length_nil,List.length_cons,if_true]
            simp only [List.length_cons] at frontLength
            omega
          · simp only [after,List.length_nil,List.length_cons,if_true]
            omega

end DynamicOptimality.SingleFinger.SourceDeque

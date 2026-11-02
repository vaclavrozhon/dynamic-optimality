import DynamicOptimality.SingleFinger.SourceDequeTransferLeft
import DynamicOptimality.SingleFinger.SourceDequeAbsorb

/-! Catenate by repeatedly moving the maximum inner cell into the minimum
end of the outer deque. The remaining first gap stays unchanged. Together
with right catenation and port interchange, this permits smaller-side work.
-/

namespace DynamicOptimality.SingleFinger.SourceDequeCatenateLeft

open ChaCha.Paper20261030 ColoredStorage SourcePointer SourceLocalProgram
open SourceSpine SourceCounted SourceBoundary SourceOpenDeque SourceDequeTransferLeft

variable {α ρ : Type*}

def plan (doubled : Bool) (front back : Nat) (rest : Schedule) : Schedule :=
  if empty : front+back = 0 then Left.prependPlan doubled rest
  else SourceDequeTransferLeft.plan doubled front back
    (plan true (nextFront front back) (nextBack front back) rest)
termination_by front+back
decreasing_by have := next_size (front := front) (back := back) (by omega); omega

theorem execute (outer : Left α ρ) (inner : SourceDeque.Layout α ρ)
    (outside : List (Frame α ρ)) (rest : Schedule) :
    ∃ (after : Left α ρ) (cost : Nat),
      Steps code (plan outer.doubled inner.front.length inner.back.length rest)
        ⟨(outer.fill inner.tree).tree,outside⟩ rest
        ⟨(after.fill inner.gap).tree,outside⟩ [] cost ∧
      cost+after.potential ≤ outer.potential+inner.potential+28*inner.cells.length ∧
      after = outer.absorb inner.cells := by
  by_cases empty : inner.front.length+inner.back.length = 0
  · have frontNil : inner.front = [] := by
      apply List.length_eq_zero_iff.mp
      omega
    have backNil : inner.back = [] := by
      apply List.length_eq_zero_iff.mp
      omega
    rcases inner with ⟨gap,front,pivot,afterGap,back⟩
    dsimp only at frontNil backNil
    subst front
    subst back
    refine ⟨outer.prepend afterGap pivot,transportCost outer.doubled+1,?_,?_,rfl⟩
    · rw [plan,dif_pos empty]
      simpa only [List.length_nil,Nat.zero_add,ite_true,SourceDeque.Layout.tree,rightSpine,leftSpine]
        using outer.prepend_run gap pivot afterGap outside rest
    · have bound := outer.prepend_amortized afterGap pivot
      simpa only [SourceDeque.Layout.potential,SourceDeque.potential,List.length_nil,
        SourceDeque.Layout.cells,List.nil_append,List.length_cons] using
        (by omega : transportCost outer.doubled+1+(outer.prepend afterGap pivot).potential ≤
          outer.potential+0+28*1)
  · have enough : 2 ≤ inner.cells.length := by
      simp only [SourceDeque.Layout.cells,List.length_append,List.length_cons]
      omega
    let tail := plan true (nextFront inner.front.length inner.back.length)
      (nextBack inner.front.length inner.back.length) rest
    obtain ⟨middle,entry,gap,firstCost,cells,initial,firstRun,firstBound,frontLength,backLength⟩ :=
      SourceDequeTransferLeft.execute outer inner enough outside tail
    obtain ⟨after,lastCost,lastRun,lastBound,lastSame⟩ :=
      execute (outer.prepend gap entry) middle outside rest
    have shorter : middle.cells.length+1 = inner.cells.length := by
      rw [cells]
      simp
    have doubled : (outer.prepend gap entry).doubled = true := rfl
    rw [doubled,frontLength,backLength,initial] at lastRun
    refine ⟨after,firstCost+lastCost,?_,?_,?_⟩
    · rw [plan,dif_neg empty]
      simpa only [tail,List.nil_append] using firstRun.append lastRun
    · omega
    · rw [lastSame,cells,Left.absorb_append]
termination_by inner.cells.length
decreasing_by
  have lengths := congrArg List.length cells
  simp only [List.length_append,List.length_singleton] at lengths
  omega

end DynamicOptimality.SingleFinger.SourceDequeCatenateLeft

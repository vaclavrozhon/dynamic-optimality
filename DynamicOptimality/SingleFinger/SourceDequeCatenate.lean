import DynamicOptimality.SingleFinger.SourceDequeTransfer
import DynamicOptimality.SingleFinger.SourceDequeAbsorb

/-! Catenation by transferring the entire inner deque. Its implementation is
online: the executable schedule is determined by spine lengths, and reads no
source tree or future request. The bound retains the sum of queue potentials.
Choosing the smaller side requires the constant-size interchange kernel.
-/

namespace DynamicOptimality.SingleFinger.SourceDequeCatenate

open ChaCha.Paper20261030 ColoredStorage SourcePointer SourceLocalProgram
open DynamicOptimality.LocalProgram (Move)
open SourceSpine SourceCounted SourceBoundary SourceOpenDeque SourceDequeTransfer

variable {α ρ : Type*}

def plan (doubled : Bool) (front back : Nat) (rest : Schedule) : Schedule :=
  if empty : front+back = 0 then Right.appendPlan doubled rest
  else SourceDequeTransfer.plan doubled front back
    (plan true (nextFront front back) (nextBack front back) rest)
termination_by front+back
decreasing_by have := next_size (front := front) (back := back) (by omega); omega

/-- The budget is linear in the number of cells actually transferred, not
in the size of the large receiving deque or any hanging subtree. -/
theorem execute (outer : Right α ρ) (inner : SourceDeque.Layout α ρ)
    (outside : List (Frame α ρ)) (rest : Schedule) :
    ∃ (after : Right α ρ) (cost : Nat),
      Steps code (plan outer.back.isSome inner.front.length inner.back.length rest)
        ⟨(outer.fill inner.tree).tree,outside⟩ rest
        ⟨(after.fill inner.terminal).tree,outside⟩ [] cost ∧
      cost+after.potential ≤ outer.potential+inner.potential+28*inner.cells.length ∧
      after = outer.absorb inner.gap inner.cells := by
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
    refine ⟨outer.append gap pivot,transportCost outer.back.isSome+1,?_,?_,rfl⟩
    · rw [plan,dif_pos empty]
      simpa only [List.length_nil,Nat.zero_add,ite_true,SourceDeque.Layout.tree,SourceDeque.Layout.terminal,
        SourceDeque.Layout.cells,SourceDeque.trailing,rightSpine,leftSpine,List.nil_append]
        using outer.append_run gap pivot afterGap outside rest
    · have bound := outer.append_amortized gap pivot
      simpa only [SourceDeque.Layout.potential,SourceDeque.potential,List.length_nil,
        SourceDeque.Layout.cells,List.nil_append,List.length_cons] using
        (by omega : transportCost outer.back.isSome+1+(outer.append gap pivot).potential ≤
          outer.potential+0+28*1)
  · have enough : 2 ≤ inner.cells.length := by
      simp only [SourceDeque.Layout.cells,List.length_append,List.length_cons]
      omega
    let tail := plan true (nextFront inner.front.length inner.back.length)
      (nextBack inner.front.length inner.back.length) rest
    obtain ⟨middle,entry,firstCost,cells,firstRun,firstBound,frontLength,backLength⟩ :=
      SourceDequeTransfer.execute outer inner enough outside tail
    obtain ⟨after,lastCost,lastRun,lastBound,lastSame⟩ :=
      execute (outer.append inner.gap entry) middle outside rest
    have terminal := SourceDeque.terminal_of_pop cells
    have shorter : middle.cells.length+1 = inner.cells.length := by
      rw [cells]
      simp
    have doubled : (outer.append inner.gap entry).back.isSome = true := rfl
    rw [doubled,frontLength,backLength,← terminal] at lastRun
    refine ⟨after,firstCost+lastCost,?_,?_,?_⟩
    · rw [plan,dif_neg empty]
      simpa only [tail,List.nil_append] using firstRun.append lastRun
    · omega
    · rw [lastSame,cells]
      rfl
termination_by inner.cells.length
decreasing_by
  have lengths := congrArg List.length cells
  simp only [List.length_cons] at lengths
  omega

end DynamicOptimality.SingleFinger.SourceDequeCatenate

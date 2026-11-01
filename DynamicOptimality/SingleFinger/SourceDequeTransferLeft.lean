import DynamicOptimality.SingleFinger.SourceOpenLeftDeque
import DynamicOptimality.SingleFinger.SourceDequePopMax

/-! The maximum-to-minimum counterpart of `SourceDequeTransfer`: extract
one maximum cell from the inner deque and insert it into the outer deque.
All traversals occur along the two constant-depth external ports.
-/

namespace DynamicOptimality.SingleFinger.SourceDequeTransferLeft

open TangoSquared.Paper20261030 ColoredStorage SourcePointer SourceLocalProgram
open SourceSpine SourceCounted SourceBoundary SourceOpenDeque

variable {α ρ : Type*}

def depth (doubled : Bool) : Nat := if doubled then 2 else 1

def nextFront (front back : Nat) : Nat :=
  if back = 0 then if front = 1 then 0 else (front+1)/2 else front

def nextBack (front back : Nat) : Nat :=
  if back = 0 then front-(front+1)/2-1 else back-1

def plan (doubled : Bool) (front back : Nat) (rest : Schedule) : Schedule :=
  prepend .left (depth doubled)
    (SourceDeque.popMaxPlan front back
      (prepend .up 1 (prepend .up (depth doubled) (Left.prependPlan doubled rest))))

theorem port_depth (layout : Left α ρ) : layout.port.depth = depth layout.doubled := by
  simp only [LeftPort.depth,Left.port_tag,depth]

theorem next_size {front back : Nat} (nonempty : 0 < front+back) :
    nextFront front back + nextBack front back + 1 = front+back := by
  unfold nextFront nextBack
  split <;> (try split_ifs) <;> omega

theorem execute (outer : Left α ρ) (inner : SourceDeque.Layout α ρ)
    (enough : 2 ≤ inner.cells.length)
    (outside : List (Frame α ρ)) (rest : Schedule) :
    ∃ (after : SourceDeque.Layout α ρ) (entry : ρ) (gap : Source α ρ) (cost : Nat),
      inner.cells = after.cells++[(entry,gap)] ∧ after.gap = inner.gap ∧
      Steps code (plan outer.doubled inner.front.length inner.back.length rest)
        ⟨(outer.fill inner.tree).tree,outside⟩ rest
        ⟨((outer.prepend gap entry).fill after.tree).tree,outside⟩ [] cost ∧
      cost + (outer.prepend gap entry).potential + after.potential ≤
        outer.potential+inner.potential+28 ∧
      after.front.length = nextFront inner.front.length inner.back.length ∧
      after.back.length = nextBack inner.front.length inner.back.length := by
  let finish := Left.prependPlan outer.doubled rest
  let back := prepend .up 1 (prepend .up outer.port.depth finish)
  obtain ⟨after,entry,gap,popCost,cells,initial,popRun,popBound,frontLength,backLength⟩ :=
    SourceDeque.pop_max inner enough (outer.port.frames++outside) back
  have enter := outer.port.enter inner.tree outside
    (SourceDeque.popMaxPlan inner.front.length inner.back.length back)
  have up := SourceCounted.one (α := α) (ρ := ρ) (action := .up)
    (before := ⟨after.tree,.left entry gap::(outer.port.frames++outside)⟩)
    rfl (prepend .up outer.port.depth finish)
  have leave := outer.port.leave (node after.tree entry gap) outside finish
  have append := outer.prepend_run after.tree entry gap outside rest
  rw [outer.fill_tree (node after.tree entry gap)] at append
  have run := enter.append (popRun.append (up.append (leave.append append)))
  refine ⟨after,entry,gap,outer.port.depth+(popCost+(1+(outer.port.depth+
    (transportCost outer.doubled+1)))),cells,initial,?_,?_,frontLength,backLength⟩
  · simpa only [plan,back,finish,port_depth,← Left.fill_tree,List.nil_append] using run
  · have enterBound := outer.port.bounded
    have appendBound := outer.prepend_amortized gap entry
    omega

end DynamicOptimality.SingleFinger.SourceDequeTransferLeft

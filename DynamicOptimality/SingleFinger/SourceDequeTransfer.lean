import DynamicOptimality.SingleFinger.SourceOpenDeque
import DynamicOptimality.SingleFinger.SourceDequePop

/-! Transfer one cell from a deque nested in another deque's maximum gap.
The entire operation is an actual source-local controller prefix. Its cost
plus both final queue potentials is at most both initial potentials plus 28.
The returned spine lengths are computed from the old lengths, so repetition
requires no ghost tree information or address oracle.
-/

namespace DynamicOptimality.SingleFinger.SourceDequeTransfer

open ChaCha.Paper20261030 ColoredStorage SourcePointer SourceLocalProgram
open DynamicOptimality.LocalProgram (Move)
open SourceSpine SourceCounted SourceBoundary SourceOpenDeque

variable {α ρ : Type*}

def depth (doubled : Bool) : Nat := if doubled then 2 else 1

def nextFront (front back : Nat) : Nat := if front = 0 then (back+1)/2-1 else front-1
def nextBack (front back : Nat) : Nat := if front = 0 then back-(back+1)/2 else back

def plan (doubled : Bool) (front back : Nat) (rest : Schedule) : Schedule :=
  prepend .right (depth doubled)
    (SourceDeque.popMinPlan front back
      (prepend .up 1 (prepend .up (depth doubled) (Right.appendPlan doubled rest))))

theorem port_depth (layout : Right α ρ) : layout.port.depth = depth layout.back.isSome := by
  simp only [RightPort.depth,Right.port_tag,depth]

theorem next_size {front back : Nat} (nonempty : 0 < front+back) :
    nextFront front back + nextBack front back + 1 = front+back := by
  unfold nextFront nextBack
  split <;> omega

theorem execute (outer : Right α ρ) (inner : SourceDeque.Layout α ρ)
    (enough : 2 ≤ inner.cells.length)
    (outside : List (Frame α ρ)) (rest : Schedule) :
    ∃ (after : SourceDeque.Layout α ρ) (entry : ρ) (cost : Nat),
      inner.cells = (entry,after.gap)::after.cells ∧
      Steps code (plan outer.back.isSome inner.front.length inner.back.length rest)
        ⟨(outer.fill inner.tree).tree,outside⟩ rest
        ⟨((outer.append inner.gap entry).fill after.tree).tree,outside⟩ [] cost ∧
      cost + (outer.append inner.gap entry).potential + after.potential ≤
        outer.potential+inner.potential+28 ∧
      after.front.length = nextFront inner.front.length inner.back.length ∧
      after.back.length = nextBack inner.front.length inner.back.length := by
  let finish := Right.appendPlan outer.back.isSome rest
  let back := prepend .up 1 (prepend .up outer.port.depth finish)
  obtain ⟨after,entry,popCost,cells,popRun,popBound,frontLength,backLength⟩ :=
    SourceDeque.pop_min inner enough (outer.port.frames++outside) back
  have enter := outer.port.enter inner.tree outside
    (SourceDeque.popMinPlan inner.front.length inner.back.length back)
  have up := SourceCounted.one (α := α) (ρ := ρ) (action := .up)
    (before := ⟨after.tree,.right inner.gap entry::(outer.port.frames++outside)⟩)
    rfl (prepend .up outer.port.depth finish)
  have leave := outer.port.leave (node inner.gap entry after.tree) outside finish
  have append := outer.append_run inner.gap entry after.tree outside rest
  rw [outer.fill_tree (node inner.gap entry after.tree)] at append
  have run := enter.append (popRun.append (up.append (leave.append append)))
  refine ⟨after,entry,outer.port.depth+(popCost+(1+(outer.port.depth+
    (transportCost outer.back.isSome+1)))),cells,?_,?_,frontLength,backLength⟩
  · simpa only [plan,back,finish,port_depth,← Right.fill_tree,List.nil_append] using run
  · have enterBound := outer.port.bounded
    have appendBound := outer.append_amortized inner.gap entry
    omega

end DynamicOptimality.SingleFinger.SourceDequeTransfer

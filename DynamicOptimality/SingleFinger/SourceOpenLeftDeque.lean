import DynamicOptimality.SingleFinger.SourcePortRotation

/-! A deque with a variable minimum-side gap. The four fields describe
the unchanged queue; the variable subtree is supplied only in the ghost
representation. The executable insertion uses at most five adjacent moves.
-/

namespace DynamicOptimality.SingleFinger.SourceOpenDeque

open TangoSquared.Paper20261030 ColoredStorage SourcePointer SourceLocalProgram
open SourceSpine SourceCounted SourceBoundary

variable {α ρ : Type*}

structure Left (α ρ : Type*) where
  front : List (Cell α ρ)
  pivot : ρ
  afterGap : Source α ρ
  back : List (Cell α ρ)

def Left.fill (layout : Left α ρ) (firstGap : Source α ρ) : SourceDeque.Layout α ρ :=
  ⟨firstGap,layout.front,layout.pivot,layout.afterGap,layout.back⟩

def Left.port (layout : Left α ρ) : LeftPort α ρ :=
  ⟨layout.pivot,leftSpine layout.afterGap layout.back,
    match layout.front with
    | [] => none
    | (entry,gap)::rest => some (entry,rightSpine gap rest)⟩

def Left.doubled (layout : Left α ρ) : Bool := !layout.front.isEmpty

def Left.potential (layout : Left α ρ) : Nat :=
  SourceDeque.potential layout.front.length layout.back.length

theorem Left.fill_tree (layout : Left α ρ) (firstGap : Source α ρ) :
    (layout.fill firstGap).tree = layout.port.fill firstGap := by
  rcases layout with ⟨front,pivot,afterGap,back⟩
  cases front with
  | nil => rfl
  | cons cell front => cases cell; rfl

theorem Left.fill_potential (layout : Left α ρ) (firstGap : Source α ρ) :
    (layout.fill firstGap).potential = layout.potential := rfl

theorem Left.port_tag (layout : Left α ρ) : layout.port.middle.isSome = layout.doubled := by
  cases layout with | mk front pivot afterGap back => cases front <;> rfl

def Left.prepend (layout : Left α ρ) (afterGap : Source α ρ) (entry : ρ) : Left α ρ :=
  { layout with front := (entry,afterGap)::layout.front }

theorem Left.prepend_fill (layout : Left α ρ) (beforeGap : Source α ρ) (entry : ρ)
    (afterGap : Source α ρ) :
    (layout.prepend afterGap entry).fill beforeGap =
      SourceDeque.pushMinLayout (layout.fill afterGap) entry beforeGap := rfl

theorem Left.prepend_potential (layout : Left α ρ) (afterGap : Source α ρ) (entry : ρ) :
    (layout.prepend afterGap entry).potential ≤ layout.potential+4 := by
  have bound := SourceDeque.push_min_amortized (layout.fill afterGap) entry afterGap
  rw [← layout.prepend_fill afterGap entry afterGap,
    Left.fill_potential,Left.fill_potential] at bound
  omega

def Left.prependPlan (doubled : Bool) (rest : Schedule) : Schedule :=
  extractPlan false doubled (SourceCounted.prepend .rotateLeft 1 rest)

theorem Left.prepend_run (layout : Left α ρ) (beforeGap : Source α ρ) (entry : ρ)
    (afterGap : Source α ρ) (outside : List (Frame α ρ)) (rest : Schedule) :
    Steps code (Left.prependPlan layout.doubled rest)
      ⟨(layout.fill (node beforeGap entry afterGap)).tree,outside⟩ rest
      ⟨((layout.prepend afterGap entry).fill beforeGap).tree,outside⟩ []
      (transportCost layout.doubled+1) := by
  have first := layout.port.extract beforeGap entry afterGap outside
    (SourceCounted.prepend .rotateLeft 1 rest)
  have last := SourceDeque.push_min (layout.fill afterGap) entry beforeGap outside rest
  rw [layout.fill_tree afterGap] at last
  have run := first.append last
  simpa only [Left.prependPlan,← Left.fill_tree,Left.port_tag,← Left.prepend_fill,
    List.nil_append] using run

theorem Left.prepend_amortized (layout : Left α ρ) (afterGap : Source α ρ) (entry : ρ) :
    transportCost layout.doubled+1+(layout.prepend afterGap entry).potential ≤
      layout.potential+9 := by
  have cost := transportCost_bound layout.doubled
  have potential := layout.prepend_potential afterGap entry
  omega

end DynamicOptimality.SingleFinger.SourceOpenDeque

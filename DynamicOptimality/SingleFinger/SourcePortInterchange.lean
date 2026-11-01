import DynamicOptimality.SingleFinger.SourcePortRotation

/-! Interchange two adjacent deque contexts in constant physical time.
This lets catenation keep the larger deque and transfer the smaller one.
Each context has depth at most two; no queue interior is traversed.
-/

namespace DynamicOptimality.SingleFinger.SourceBoundary

open TangoSquared.Paper20261030 ColoredStorage SourcePointer SourceLocalProgram
open DynamicOptimality.LocalProgram (Move)
open SourceSpine SourceCounted

variable {α ρ : Type*}

def interchangePlan (lowDouble highDouble : Bool) (rest : Schedule) : Schedule :=
  if highDouble then extractPlan true lowDouble
    (prepend .left 1 (extractPlan true lowDouble (prepend .up 1 rest)))
  else extractPlan true lowDouble rest

def interchangeCost (lowDouble highDouble : Bool) : Nat :=
  if highDouble then 2*transportCost lowDouble+2 else transportCost lowDouble

theorem interchangeCost_bound (lowDouble highDouble : Bool) :
    interchangeCost lowDouble highDouble ≤ 10 := by
  have bound := transportCost_bound lowDouble
  unfold interchangeCost
  split <;> omega

theorem interchange (low : RightPort α ρ) (high : LeftPort α ρ) (gap : Source α ρ)
    (outside : List (Frame α ρ)) (rest : Schedule) :
    Steps code (interchangePlan low.middle.isSome high.middle.isSome rest)
      ⟨low.fill (high.fill gap),outside⟩ rest
      ⟨high.fill (low.fill gap),outside⟩ []
      (interchangeCost low.middle.isSome high.middle.isSome) := by
  rcases high with ⟨pivot,right,middle⟩
  cases middle with
  | none => exact low.extract gap pivot right outside rest
  | some cell =>
    rcases cell with ⟨entry,inside⟩
    have first := low.extract (node gap entry inside) pivot right outside
      (prepend .left 1 (extractPlan true low.middle.isSome (prepend .up 1 rest)))
    have down := SourceCounted.one (α := α) (ρ := ρ) (action := .left)
      (before := ⟨node (low.fill (node gap entry inside)) pivot right,outside⟩)
      rfl (extractPlan true low.middle.isSome (prepend .up 1 rest))
    have middle := low.extract gap entry inside (.left pivot right::outside) (prepend .up 1 rest)
    have up := SourceCounted.one (α := α) (ρ := ρ) (action := .up)
      (before := ⟨node (low.fill gap) entry inside,.left pivot right::outside⟩) rfl rest
    have run := first.append (down.append (middle.append up))
    simpa only [interchangePlan,interchangeCost,Option.isSome_some,ite_true,LeftPort.fill,
      List.nil_append,show transportCost low.middle.isSome+(1+(transportCost low.middle.isSome+1)) =
        2*transportCost low.middle.isSome+2 by omega] using run

end DynamicOptimality.SingleFinger.SourceBoundary

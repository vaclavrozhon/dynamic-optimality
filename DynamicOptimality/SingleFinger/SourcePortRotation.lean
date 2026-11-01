import DynamicOptimality.SingleFinger.SourceBoundary

/-! Moving an endpoint across the constant-depth external gap of a deque.
The neighboring deque's shape is retained exactly. These four-move kernels
supply the local transport needed when an endpoint changes tendon queues.
-/

namespace DynamicOptimality.SingleFinger.SourceBoundary

open TangoSquared.Paper20261030 ColoredStorage SourcePointer SourceLocalProgram
open DynamicOptimality.LocalProgram (Move)
open SourceSpine SourceCounted

variable {α ρ : Type*}

def extractPlan (right doubled : Bool) (rest : Schedule) : Schedule :=
  let rotate := if right then Move.rotateLeft else Move.rotateRight
  let descend : DynamicOptimality.LocalProgram.Move := if right then .right else .left
  if doubled then
    prepend descend 1 (prepend rotate 1 (prepend .up 1 (prepend rotate 1 rest)))
  else prepend rotate 1 rest

def insertPlan (right doubled : Bool) (rest : Schedule) : Schedule :=
  let rotate := if right then Move.rotateRight else Move.rotateLeft
  let descend : DynamicOptimality.LocalProgram.Move := if right then .right else .left
  if doubled then
    prepend rotate 1 (prepend descend 1 (prepend rotate 1 (prepend .up 1 rest)))
  else prepend rotate 1 rest

def transportCost (doubled : Bool) : Nat := if doubled then 4 else 1

theorem transportCost_bound (doubled : Bool) : transportCost doubled ≤ 4 := by
  cases doubled <;> decide

theorem RightPort.extract (port : RightPort α ρ) (left : Source α ρ) (entry : ρ) (right : Source α ρ)
    (outside : List (Frame α ρ)) (rest : Schedule) :
    Steps code (extractPlan true port.middle.isSome rest)
      ⟨port.fill (node left entry right),outside⟩ rest
      ⟨node (port.fill left) entry right,outside⟩ [] (transportCost port.middle.isSome) := by
  cases port with | mk a x middle => cases middle with
    | none => exact SourceCounted.one (action := .rotateLeft) rfl rest
    | some cell =>
      rcases cell with ⟨b,y⟩
      apply Steps.next (entry := none) (cost := 3)
      · exact .nav (action := .right) rfl rfl
      apply Steps.next (entry := none) (cost := 2)
      · exact .nav (action := .rotateLeft) rfl rfl
      apply Steps.next (entry := none) (cost := 1)
      · exact .nav (action := .up) rfl rfl
      exact SourceCounted.one (action := .rotateLeft) rfl rest

theorem LeftPort.extract (port : LeftPort α ρ) (left : Source α ρ) (entry : ρ) (right : Source α ρ)
    (outside : List (Frame α ρ)) (rest : Schedule) :
    Steps code (extractPlan false port.middle.isSome rest)
      ⟨port.fill (node left entry right),outside⟩ rest
      ⟨node left entry (port.fill right),outside⟩ [] (transportCost port.middle.isSome) := by
  cases port with | mk x c middle => cases middle with
    | none => exact SourceCounted.one (action := .rotateRight) rfl rest
    | some cell =>
      rcases cell with ⟨y,b⟩
      apply Steps.next (entry := none) (cost := 3)
      · exact .nav (action := .left) rfl rfl
      apply Steps.next (entry := none) (cost := 2)
      · exact .nav (action := .rotateRight) rfl rfl
      apply Steps.next (entry := none) (cost := 1)
      · exact .nav (action := .up) rfl rfl
      exact SourceCounted.one (action := .rotateRight) rfl rest

theorem RightPort.insert (port : RightPort α ρ) (left : Source α ρ) (entry : ρ) (right : Source α ρ)
    (outside : List (Frame α ρ)) (rest : Schedule) :
    Steps code (insertPlan true port.middle.isSome rest)
      ⟨node (port.fill left) entry right,outside⟩ rest
      ⟨port.fill (node left entry right),outside⟩ [] (transportCost port.middle.isSome) := by
  cases port with | mk a x middle => cases middle with
    | none => exact SourceCounted.one (action := .rotateRight) rfl rest
    | some cell =>
      rcases cell with ⟨b,y⟩
      apply Steps.next (entry := none) (cost := 3)
      · exact .nav (action := .rotateRight) rfl rfl
      apply Steps.next (entry := none) (cost := 2)
      · exact .nav (action := .right) rfl rfl
      apply Steps.next (entry := none) (cost := 1)
      · exact .nav (action := .rotateRight) rfl rfl
      exact SourceCounted.one (action := .up) rfl rest

theorem LeftPort.insert (port : LeftPort α ρ) (left : Source α ρ) (entry : ρ) (right : Source α ρ)
    (outside : List (Frame α ρ)) (rest : Schedule) :
    Steps code (insertPlan false port.middle.isSome rest)
      ⟨node left entry (port.fill right),outside⟩ rest
      ⟨port.fill (node left entry right),outside⟩ [] (transportCost port.middle.isSome) := by
  cases port with | mk x c middle => cases middle with
    | none => exact SourceCounted.one (action := .rotateLeft) rfl rest
    | some cell =>
      rcases cell with ⟨y,b⟩
      apply Steps.next (entry := none) (cost := 3)
      · exact .nav (action := .rotateLeft) rfl rfl
      apply Steps.next (entry := none) (cost := 2)
      · exact .nav (action := .left) rfl rfl
      apply Steps.next (entry := none) (cost := 1)
      · exact .nav (action := .rotateLeft) rfl rfl
      exact SourceCounted.one (action := .up) rfl rest

end DynamicOptimality.SingleFinger.SourceBoundary

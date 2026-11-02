import DynamicOptimality.SingleFinger.SourceDequeEndpoints

/-! The two external gaps of a deque are at depth at most two. These local
programs enter or leave either gap using only a two-valued length counter.
This is the constant-depth connection used to nest the two deques of a tendon.
The port objects themselves are ghost descriptions of unchanged subtrees.
-/

namespace DynamicOptimality.SingleFinger.SourceBoundary

open ChaCha.Paper20261030 ColoredStorage SourcePointer SourceLocalProgram
open DynamicOptimality.LocalProgram (Move)
open SourceSpine SourceCounted

variable {α ρ : Type*}

structure LeftPort (α ρ : Type*) where
  pivot : ρ
  right : Source α ρ
  middle : Option (ρ × Source α ρ)

structure RightPort (α ρ : Type*) where
  left : Source α ρ
  pivot : ρ
  middle : Option (Source α ρ × ρ)

def LeftPort.fill (port : LeftPort α ρ) (gap : Source α ρ) : Source α ρ :=
  match port.middle with
  | none => node gap port.pivot port.right
  | some (entry,right) => node (node gap entry right) port.pivot port.right

def RightPort.fill (port : RightPort α ρ) (gap : Source α ρ) : Source α ρ :=
  match port.middle with
  | none => node port.left port.pivot gap
  | some (left,entry) => node port.left port.pivot (node left entry gap)

def LeftPort.frames (port : LeftPort α ρ) : List (Frame α ρ) :=
  match port.middle with
  | none => [.left port.pivot port.right]
  | some (entry,right) => [.left entry right,.left port.pivot port.right]

def RightPort.frames (port : RightPort α ρ) : List (Frame α ρ) :=
  match port.middle with
  | none => [.right port.left port.pivot]
  | some (left,entry) => [.right left entry,.right port.left port.pivot]

def LeftPort.depth (port : LeftPort α ρ) : Nat := if port.middle.isSome then 2 else 1
def RightPort.depth (port : RightPort α ρ) : Nat := if port.middle.isSome then 2 else 1

theorem LeftPort.bounded (port : LeftPort α ρ) : port.depth ≤ 2 := by
  cases port with | mk pivot right middle => cases middle <;> simp [LeftPort.depth]

theorem RightPort.bounded (port : RightPort α ρ) : port.depth ≤ 2 := by
  cases port with | mk left pivot middle => cases middle <;> simp [RightPort.depth]

theorem LeftPort.plug (port : LeftPort α ρ) (gap : Source α ρ) :
    SourcePointer.plug gap port.frames = port.fill gap := by
  cases port with | mk pivot right middle => cases middle with
    | none => rfl
    | some cell => cases cell; rfl

theorem RightPort.plug (port : RightPort α ρ) (gap : Source α ρ) :
    SourcePointer.plug gap port.frames = port.fill gap := by
  cases port with | mk left pivot middle => cases middle with
    | none => rfl
    | some cell => cases cell; rfl

theorem LeftPort.enter (port : LeftPort α ρ) (gap : Source α ρ)
    (outside : List (Frame α ρ)) (rest : Schedule) :
    Steps code (prepend .left port.depth rest) ⟨port.fill gap,outside⟩ rest
      ⟨gap,port.frames++outside⟩ [] port.depth := by
  cases port with | mk pivot right middle => cases middle with
    | none => exact SourceCounted.one rfl rest
    | some cell =>
      rcases cell with ⟨entry,rightInside⟩
      apply Steps.next (entry := none) (cost := 1)
      · exact .nav rfl rfl
      exact SourceCounted.one rfl rest

theorem RightPort.enter (port : RightPort α ρ) (gap : Source α ρ)
    (outside : List (Frame α ρ)) (rest : Schedule) :
    Steps code (prepend .right port.depth rest) ⟨port.fill gap,outside⟩ rest
      ⟨gap,port.frames++outside⟩ [] port.depth := by
  cases port with | mk left pivot middle => cases middle with
    | none => exact SourceCounted.one rfl rest
    | some cell =>
      rcases cell with ⟨leftInside,entry⟩
      apply Steps.next (entry := none) (cost := 1)
      · exact .nav rfl rfl
      exact SourceCounted.one rfl rest

theorem LeftPort.leave (port : LeftPort α ρ) (gap : Source α ρ)
    (outside : List (Frame α ρ)) (rest : Schedule) :
    Steps code (prepend .up port.depth rest) ⟨gap,port.frames++outside⟩ rest
      ⟨port.fill gap,outside⟩ [] port.depth := by
  cases port with | mk pivot right middle => cases middle with
    | none => exact SourceCounted.one rfl rest
    | some cell =>
      rcases cell with ⟨entry,rightInside⟩
      apply Steps.next (entry := none) (cost := 1)
      · exact .nav rfl rfl
      exact SourceCounted.one rfl rest

theorem RightPort.leave (port : RightPort α ρ) (gap : Source α ρ)
    (outside : List (Frame α ρ)) (rest : Schedule) :
    Steps code (prepend .up port.depth rest) ⟨gap,port.frames++outside⟩ rest
      ⟨port.fill gap,outside⟩ [] port.depth := by
  cases port with | mk left pivot middle => cases middle with
    | none => exact SourceCounted.one rfl rest
    | some cell =>
      rcases cell with ⟨leftInside,entry⟩
      apply Steps.next (entry := none) (cost := 1)
      · exact .nav rfl rfl
      exact SourceCounted.one rfl rest

/-- A deque's first inorder gap is precisely a left port. -/
def minimumPort (layout : SourceDeque.Layout α ρ) : LeftPort α ρ :=
  ⟨layout.pivot,leftSpine layout.afterGap layout.back,
    match layout.front with
    | [] => none
    | (entry,nextGap)::front => some (entry,rightSpine nextGap front)⟩

theorem minimumPort_fill (layout : SourceDeque.Layout α ρ) :
    (minimumPort layout).fill layout.gap = layout.tree := by
  rcases layout with ⟨gap,front,pivot,afterGap,back⟩
  cases front with
  | nil => rfl
  | cons cell front => cases cell; rfl

/-- A deque's last inorder gap is precisely a right port. The statement
also retains the gap itself, so it can contain the second deque or a leaf. -/
theorem maximumPort_exists (layout : SourceDeque.Layout α ρ) :
    ∃ (port : RightPort α ρ) (gap : Source α ρ),
      port.fill gap = layout.tree ∧ port.depth = (if layout.back.length = 0 then 1 else 2) := by
  rcases layout with ⟨gap,front,pivot,afterGap,back⟩
  induction back using List.reverseRecOn with
  | nil => exact ⟨⟨rightSpine gap front,pivot,none⟩,afterGap,rfl,rfl⟩
  | append_singleton back cell ih =>
    rcases cell with ⟨entry,lastGap⟩
    refine ⟨⟨rightSpine gap front,pivot,some (leftSpine afterGap back,entry)⟩,lastGap,?_,?_⟩
    · simp only [RightPort.fill,SourceDeque.Layout.tree,leftSpine_append,leftSpine]
    · simp [RightPort.depth]

end DynamicOptimality.SingleFinger.SourceBoundary

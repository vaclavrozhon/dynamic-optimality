import DynamicOptimality.SingleFinger.SourcePortRotation

/-! A deque with a variable maximum-side gap. The gap may contain another
deque, a bottom skeleton vertex, or an arbitrary unchanged source subtree.
An endpoint entering at this gap is inserted with at most five actual local
operations and at most nine amortized operations. No stored subtree is read.
-/

namespace DynamicOptimality.SingleFinger.SourceOpenDeque

open TangoSquared.Paper20261030 ColoredStorage SourcePointer SourceLocalProgram
open DynamicOptimality.LocalProgram (Move)
open SourceSpine SourceCounted SourceBoundary

variable {α ρ : Type*}

/-- The optional back spine stores its final record separately because the
subtree following that record is the variable gap. This is a ghost layout. -/
structure Right (α ρ : Type*) where
  gap : Source α ρ
  front : List (Cell α ρ)
  pivot : ρ
  back : Option (Source α ρ × List (Cell α ρ) × ρ)

def Right.fill (layout : Right α ρ) (lastGap : Source α ρ) : SourceDeque.Layout α ρ :=
  match layout.back with
  | none => ⟨layout.gap,layout.front,layout.pivot,lastGap,[]⟩
  | some (afterGap,back,last) => ⟨layout.gap,layout.front,layout.pivot,afterGap,back++[(last,lastGap)]⟩

def Right.port (layout : Right α ρ) : RightPort α ρ :=
  ⟨rightSpine layout.gap layout.front,layout.pivot,
    layout.back.map (fun (afterGap,back,last) => (leftSpine afterGap back,last))⟩

def Right.backLength (layout : Right α ρ) : Nat :=
  match layout.back with
  | none => 0
  | some (_,back,_) => back.length+1

def Right.potential (layout : Right α ρ) : Nat :=
  SourceDeque.potential layout.front.length layout.backLength

theorem Right.fill_tree (layout : Right α ρ) (lastGap : Source α ρ) :
    (layout.fill lastGap).tree = layout.port.fill lastGap := by
  rcases layout with ⟨gap,front,pivot,back⟩
  cases back with
  | none => rfl
  | some data =>
    rcases data with ⟨afterGap,back,last⟩
    simp only [Right.fill,Right.port,Option.map_some,RightPort.fill,SourceDeque.Layout.tree,
      leftSpine_append,leftSpine]

theorem Right.fill_potential (layout : Right α ρ) (lastGap : Source α ρ) :
    (layout.fill lastGap).potential = layout.potential := by
  rcases layout with ⟨gap,front,pivot,back⟩
  cases back with
  | none => rfl
  | some data =>
    rcases data with ⟨afterGap,back,last⟩
    simp only [Right.fill,Right.potential,Right.backLength,SourceDeque.Layout.potential,
      List.length_append,List.length_singleton]

theorem Right.port_tag (layout : Right α ρ) : layout.port.middle.isSome = layout.back.isSome := by
  cases layout with | mk gap front pivot back => cases back <;> rfl

/-- Append a new greatest cell; its left gap becomes the old terminal gap. -/
def Right.append (layout : Right α ρ) (beforeGap : Source α ρ) (entry : ρ) : Right α ρ :=
  { layout with back := some (match layout.back with
    | none => (beforeGap,[],entry)
    | some (afterGap,back,last) => (afterGap,back++[(last,beforeGap)],entry)) }

theorem Right.append_fill (layout : Right α ρ) (beforeGap : Source α ρ) (entry : ρ)
    (afterGap : Source α ρ) :
    (layout.append beforeGap entry).fill afterGap =
      SourceDeque.pushMaxLayout (layout.fill beforeGap) entry afterGap := by
  rcases layout with ⟨gap,front,pivot,back⟩
  cases back with
  | none => rfl
  | some data =>
    rcases data with ⟨start,back,last⟩
    simp only [Right.append,Right.fill,SourceDeque.pushMaxLayout,List.append_assoc]

theorem Right.append_potential (layout : Right α ρ) (beforeGap : Source α ρ) (entry : ρ) :
    (layout.append beforeGap entry).potential ≤ layout.potential+4 := by
  have bound := SourceDeque.push_max_amortized (layout.fill beforeGap) entry beforeGap
  rw [← layout.append_fill beforeGap entry beforeGap,
    Right.fill_potential,Right.fill_potential] at bound
  omega

def Right.appendPlan (doubled : Bool) (rest : Schedule) : Schedule :=
  extractPlan true doubled (prepend .rotateRight 1 rest)

/-- The entering record is physically at the terminal gap. First lift it
across the one- or two-edge port, then push it into the actual deque. -/
theorem Right.append_run (layout : Right α ρ) (beforeGap : Source α ρ) (entry : ρ)
    (afterGap : Source α ρ) (outside : List (Frame α ρ)) (rest : Schedule) :
    Steps code (Right.appendPlan layout.back.isSome rest)
      ⟨(layout.fill (node beforeGap entry afterGap)).tree,outside⟩ rest
      ⟨((layout.append beforeGap entry).fill afterGap).tree,outside⟩ []
      (transportCost layout.back.isSome+1) := by
  have first := layout.port.extract beforeGap entry afterGap outside (prepend .rotateRight 1 rest)
  have last := SourceDeque.push_max (layout.fill beforeGap) entry afterGap outside rest
  rw [layout.fill_tree beforeGap] at last
  have run := first.append last
  simpa only [Right.appendPlan,← Right.fill_tree,Right.port_tag,← Right.append_fill,
    List.nil_append] using run

theorem Right.append_amortized (layout : Right α ρ) (beforeGap : Source α ρ) (entry : ρ) :
    transportCost layout.back.isSome+1+(layout.append beforeGap entry).potential ≤
      layout.potential+9 := by
  have cost := transportCost_bound layout.back.isSome
  have potential := layout.append_potential beforeGap entry
  omega

end DynamicOptimality.SingleFinger.SourceOpenDeque

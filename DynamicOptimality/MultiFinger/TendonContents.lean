import DynamicOptimality.MultiFinger.TendonSource
import DynamicOptimality.MultiFinger.TendonDeque

/-! Exact cells of the two physical half-tendons.
The invariant records the actual hanging source subtrees, not just their
inorder words. The open inner subtree may change independently as the
retained hand is restructured. -/

namespace DynamicOptimality.MultiFinger.TendonContents

open ChaCha.MTR SingleFinger
open DynamicOptimality.GeometricOnlineSimulation.OpenDeque
open TendonSource

variable {α : Type*}

def firstGap : List (LowCell α) → RawTree α → RawTree α
  | [], inside => inside
  | (left,_)::_, _ => left

def afterCells : List (LowCell α) → RawTree α → List (Spine.Cell α)
  | [], _ => []
  | (_,key)::cells, inside => (key,firstGap cells inside)::afterCells cells inside

theorem source_spine (cells : List (LowCell α)) (inside : RawTree α) :
    Spine.rightSpine (firstGap cells inside) (afterCells cells inside) = lowTree cells inside := by
  induction cells with
  | nil => rfl
  | cons cell cells ih =>
    rcases cell with ⟨left,key⟩
    simpa only [firstGap,afterCells,Spine.rightSpine,lowTree] using
      congrArg (fun tree => ChaCha.MTR.Tree.node left key tree) ih

theorem layout_word (layout : SingleFinger.Deque.Layout α) :
    layout.tree.inorder = (Spine.rightSpine layout.gap layout.cells).inorder := by
  simp [SingleFinger.Deque.Layout.tree,SingleFinger.Deque.Layout.cells,
    Spine.rightSpine_inorder,Spine.leftSpine_inorder,Tree.inorder,List.append_assoc]

def LowValid (layout : Right α) (cells : List (LowCell α)) : Prop :=
  ∀ inside, (layout.fill inside).gap = firstGap cells inside ∧
    (layout.fill inside).cells = afterCells cells inside

def HighValid (layout : Left α) (cells : List (HighCell α)) : Prop :=
  ∀ inside, (layout.fill inside).cells = cells

theorem low_word {layout : Right α} {cells : List (LowCell α)}
    (valid : LowValid layout cells) (inside : RawTree α) :
    (layout.fill inside).tree.inorder = lowWord cells++inside.inorder := by
  rw [layout_word,(valid inside).1,(valid inside).2,source_spine,lowTree_word]

theorem high_spine_word (cells : List (HighCell α)) (inside : RawTree α) :
    (Spine.rightSpine inside cells).inorder = inside.inorder++highWord cells := by
  induction cells generalizing inside with
  | nil => simp [Spine.rightSpine,highWord]
  | cons cell cells ih =>
    rcases cell with ⟨key,right⟩
    simp only [Spine.rightSpine,Tree.inorder,ih,highWord,List.append_assoc]

theorem high_word {layout : Left α} {cells : List (HighCell α)}
    (valid : HighValid layout cells) (inside : RawTree α) :
    (layout.fill inside).tree.inorder = inside.inorder++highWord cells := by
  rw [layout_word,valid inside]
  exact high_spine_word cells inside

def lowFill (layout : Option (Right α)) (inside : RawTree α) : RawTree α :=
  match layout with
  | none => inside
  | some queue => (queue.fill inside).tree

def highFill (layout : Option (Left α)) (inside : RawTree α) : RawTree α :=
  match layout with
  | none => inside
  | some queue => (queue.fill inside).tree

def LowRep : Option (Right α) → List (LowCell α) → Prop
  | none, cells => cells = []
  | some queue, cells => LowValid queue cells

def HighRep : Option (Left α) → List (HighCell α) → Prop
  | none, cells => cells = []
  | some queue, cells => HighValid queue cells

structure Tendon (α : Type*) where
  lowQueue : Option (Right α)
  highQueue : Option (Left α)

def Tendon.fill (tendon : Tendon α) (inside : RawTree α) : RawTree α :=
  lowFill tendon.lowQueue (highFill tendon.highQueue inside)

def Tendon.potential (tendon : Tendon α) : Nat :=
  (tendon.lowQueue.map Right.potential).getD 0+(tendon.highQueue.map Left.potential).getD 0

def Tendon.Represents (tendon : Tendon α) (source : List (Pointer.Frame α)) : Prop :=
  LowRep tendon.lowQueue (low source) ∧ HighRep tendon.highQueue (high source)

theorem lowFill_word {layout : Option (Right α)} {cells : List (LowCell α)}
    (valid : LowRep layout cells) (inside : RawTree α) :
    (lowFill layout inside).inorder = lowWord cells++inside.inorder := by
  cases layout with
  | none => simp only [LowRep] at valid; simp [lowFill,valid,lowWord]
  | some queue => exact low_word valid inside

theorem highFill_word {layout : Option (Left α)} {cells : List (HighCell α)}
    (valid : HighRep layout cells) (inside : RawTree α) :
    (highFill layout inside).inorder = inside.inorder++highWord cells := by
  cases layout with
  | none => simp only [HighRep] at valid; simp [highFill,valid,highWord]
  | some queue => exact high_word valid inside

/-- The compressed physical tendon has exactly the source context's
original inorder word, while every cell still holds its exact source gap. -/
theorem Tendon.word {tendon : Tendon α} {source : List (Pointer.Frame α)}
    (valid : tendon.Represents source) (inside : RawTree α) :
    (tendon.fill inside).inorder = (Pointer.plug inside source).inorder := by
  rw [Tendon.fill,lowFill_word valid.1,highFill_word valid.2,split_word,List.append_assoc]

end DynamicOptimality.MultiFinger.TendonContents

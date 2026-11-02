import ChaCha.Paper20261030.SourceReversal

/-!
# Mirroring a record-decorated routing skeleton

Mirroring reverses leaf order and exchanges left/right moves and rotation
directions, preserving actual operation cost and the observed record word.
For attached payloads, apply this to the routing skeleton before grafting
payload trees; mirroring a payload itself would reverse its key order.
-/

namespace ChaCha.Paper20261030.ColoredStorage

variable {α ρ : Type*}

def Source.mirror : Source α ρ → Source α ρ
  | .leaf key record => .leaf key record
  | .fork record l r => .fork record r.mirror l.mirror

theorem Source.mirror_mirror (t : Source α ρ) : t.mirror.mirror = t := by
  induction t <;> simp_all [mirror]

theorem Source.mirror_root (t : Source α ρ) : t.mirror.rootRecord = t.rootRecord := by cases t <;> rfl

theorem Source.mirror_setRoot (t : Source α ρ) (fresh : ρ) :
    (t.setRoot fresh).mirror = t.mirror.setRoot fresh := by cases t <;> rfl

theorem Source.mirror_leaves (t : Source α ρ) : t.mirror.shape.leaves = t.shape.leaves.reverse := by
  induction t <;> simp_all [mirror,shape,RouterProjection.Router.leaves,List.reverse_append]

end ChaCha.Paper20261030.ColoredStorage

namespace ChaCha.Paper20261030.SourcePointer

open ColoredStorage

variable {α ρ : Type*}

def Frame.mirror : Frame α ρ → Frame α ρ
  | .left record r => .right r.mirror record
  | .right l record => .left record l.mirror

def Cursor.mirror (c : Cursor α ρ) : Cursor α ρ := ⟨c.focus.mirror,c.ancestors.map Frame.mirror⟩

theorem Frame.mirror_mirror (frame : Frame α ρ) : frame.mirror.mirror = frame := by
  cases frame <;> simp only [mirror,Source.mirror_mirror]

theorem Step.mirror {a b : Cursor α ρ} (step : Step a b) : Step a.mirror b.mirror := by
  cases step with
  | left => exact .right _ _ _ _
  | right => exact .left _ _ _ _
  | upLeft => exact .upRight _ _ _ _
  | upRight => exact .upLeft _ _ _ _
  | rotateRight => exact .rotateLeft _ _ _ _ _ _
  | rotateLeft => exact .rotateRight _ _ _ _ _ _
  | write focus fresh rest => simpa only [Cursor.mirror,Source.mirror_setRoot] using Step.write focus.mirror fresh _

theorem Trace.mirror {a b : Cursor α ρ} {reads : List ρ} {cost : Nat}
    (trace : Trace a reads b cost) : Trace a.mirror reads b.mirror cost := by
  induction trace with
  | nil => exact .nil _
  | step move rest ih => exact .step move.mirror ih
  | read rest ih => simpa only [Cursor.mirror,Source.mirror_root] using Trace.read ih

theorem Rearranges.mirror {a b : Source α ρ} {budget : Nat} (h : Rearranges a b budget) :
    Rearranges a.mirror b.mirror budget := by
  intro outside
  obtain ⟨reads,cost,trace,bound⟩ := h (outside.map Frame.mirror)
  refine ⟨reads,cost,?_,bound⟩
  have same : (outside.map Frame.mirror).map Frame.mirror = outside := by
    simp only [List.map_map,Function.comp_def,Frame.mirror_mirror]
    exact List.map_id outside
  simpa only [Cursor.mirror,same] using trace.mirror

end ChaCha.Paper20261030.SourcePointer

import TangoSquared.Paper20261030.SourcePayloadCapacity
import TangoSquared.Paper20261030.SourceMirror

/-! Relabeling ports changes no routing, stored records, or charged steps.
This turns retained numeric depth ports into their actual primary exits. -/

namespace TangoSquared.Paper20261030.ColoredStorage

variable {α β ρ : Type*}

def Source.relabel (f : α → β) : Source α ρ → Source β ρ
  | .leaf key record => .leaf (f key) record
  | .fork record l r => .fork record (l.relabel f) (r.relabel f)

theorem Source.relabel_leaves (f : α → β) (t : Source α ρ) :
    (t.relabel f).shape.leaves = t.shape.leaves.map f := by
  induction t <;> simp_all [relabel,shape,RouterProjection.Router.leaves,List.map_append]

theorem Source.relabel_root (f : α → β) (t : Source α ρ) : (t.relabel f).rootRecord = t.rootRecord := by
  cases t <;> rfl

theorem Source.relabel_setRoot (f : α → β) (t : Source α ρ) (fresh : ρ) :
    (t.setRoot fresh).relabel f = (t.relabel f).setRoot fresh := by cases t <;> rfl

theorem Source.Bounded.relabel (f : α → β) {t : Source α (List ρ)} {capacity : Nat}
    (bounded : t.Bounded capacity) : (t.relabel f).Bounded capacity := by
  induction t with
  | leaf => exact bounded
  | fork records l r ihl ihr => exact ⟨bounded.1,ihl bounded.2.1,ihr bounded.2.2⟩

theorem Source.Bounded.mirror {t : Source α (List ρ)} {capacity : Nat}
    (bounded : t.Bounded capacity) : t.mirror.Bounded capacity := by
  induction t with
  | leaf => exact bounded
  | fork records l r ihl ihr => exact ⟨bounded.1,ihr bounded.2.2,ihl bounded.2.1⟩

end TangoSquared.Paper20261030.ColoredStorage

namespace TangoSquared.Paper20261030.SourcePointer

open ColoredStorage

variable {α β ρ : Type*}

def Frame.relabel (f : α → β) : Frame α ρ → Frame β ρ
  | .left record r => .left record (r.relabel f)
  | .right l record => .right (l.relabel f) record

def Cursor.relabel (f : α → β) (c : Cursor α ρ) : Cursor β ρ :=
  ⟨c.focus.relabel f,c.ancestors.map (Frame.relabel f)⟩

theorem Step.relabel (f : α → β) {a b : Cursor α ρ} (step : Step a b) :
    Step (a.relabel f) (b.relabel f) := by
  cases step with
  | left => exact .left _ _ _ _
  | right => exact .right _ _ _ _
  | upLeft => exact .upLeft _ _ _ _
  | upRight => exact .upRight _ _ _ _
  | rotateRight => exact .rotateRight _ _ _ _ _ _
  | rotateLeft => exact .rotateLeft _ _ _ _ _ _
  | write focus fresh rest => simpa only [Cursor.relabel,Source.relabel_setRoot] using Step.write (focus.relabel f) fresh _

theorem Trace.relabel (f : α → β) {a b : Cursor α ρ} {reads : List ρ} {cost : Nat}
    (trace : Trace a reads b cost) : Trace (a.relabel f) reads (b.relabel f) cost := by
  induction trace with
  | nil => exact .nil _
  | step move rest ih => exact .step (move.relabel f) ih
  | read rest ih => simpa only [Cursor.relabel,Source.relabel_root] using Trace.read ih

theorem Rearranges.relabel (f : α → β) {a b : Source α ρ} {budget : Nat}
    (execution : Rearranges a b budget) : Rearranges (a.relabel f) (b.relabel f) budget := by
  intro outside
  obtain ⟨reads,cost,trace,bound⟩ := execution []
  exact ⟨reads,cost,(trace.relabel f).extend outside,bound⟩

end TangoSquared.Paper20261030.SourcePointer

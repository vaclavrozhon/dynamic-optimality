import TangoSquared.Paper20261030.PackedReadinessComposition

/-! Basic readiness facts for structural annotations. Navigation reads
only a constant number of descriptors, and the logical leaf flag is
determined by the presence of child descriptors.
-/

namespace TangoSquared.Paper20261030.Structural

open ColoredStorage SourcePointer SourceLocalProgram PackedReadiness

variable {α ρ η C σ : Type*} [DecidableEq η] [LinearOrder C] [Fintype C]

theorem annotate_support (identifier : ρ → η) (color : α → C) (parent : Option η) (source : Source α ρ) :
    (annotate identifier color parent source).support color = source.support color := by
  induction source generalizing parent with
  | leaf => rfl
  | fork record l r ihl ihr => simp only [annotate,Source.support,ihl,ihr]

theorem fields_children_leaf (identifier : ρ → η) (color : α → C) (parent : Option η) (source : Source α ρ) :
    (fields identifier color parent source).children.isNone = isLeaf source := by
  cases source <;> rfl

theorem annotate_read_ready (identifier : ρ → η) (color : α → C) (parent : Option η)
    (source : Source α ρ) (outside) (next : (ρ × Fields η C) → Bool → σ) :
    Ready identifier color (.read next) ⟨annotate identifier color parent source,outside⟩ := by
  simp only [Ready,annotate_root,fields_children_leaf,Compiler.isLeaf_annotate]

theorem annotate_children_ready (identifier : ρ → η) (color : α → C) (parent : Option η)
    (record : ρ) (l r : Source α ρ) :
    Children identifier color (annotate identifier color parent (.fork record l r)) := by
  simp only [annotate,Children,fields,descriptor,annotate_root,annotate_support]

theorem cursor_colors_correct (identifier : ρ → η) (color : α → C) (source : Cursor α ρ) :
    ColorsCorrect (fun record => record.2.colors) color (cursor identifier color source).tree := by
  rw [cursor_tree]
  exact annotate_colors_correct identifier color none source.tree

theorem cursor_read_ready (identifier : ρ → η) (color : α → C) (source : Cursor α ρ)
    (next : (ρ × Fields η C) → Bool → σ) :
    Ready identifier color (.read next) (cursor identifier color source) :=
  annotate_read_ready identifier color _ _ _ next

theorem cursor_direct_ready (identifier : ρ → η) (color : α → C)
    (action : DynamicOptimality.LocalProgram.Move)
    (notRight : action ≠ .rotateRight) (notLeft : action ≠ .rotateLeft)
    {before after : Cursor α ρ} (moved : navigate action before = some after) (next : σ) :
    Ready identifier color (.nav action next) (cursor identifier color before) := by
  rcases before with ⟨focus,outside⟩
  cases action with
  | rotateRight => exact False.elim (notRight rfl)
  | rotateLeft => exact False.elim (notLeft rfl)
  | left => cases focus with
    | leaf => simp [navigate] at moved
    | fork record l r => exact annotate_children_ready identifier color _ record l r
  | right => cases focus with
    | leaf => simp [navigate] at moved
    | fork record l r => exact annotate_children_ready identifier color _ record l r
  | up => cases outside with
    | nil => simp [navigate] at moved
    | cons frame rest => cases frame <;>
      simp [Ready,Parent,cursor,frames,parentId,annotate_root,annotate_support,fields,descriptor]

end TangoSquared.Paper20261030.Structural

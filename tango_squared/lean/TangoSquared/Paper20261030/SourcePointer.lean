import TangoSquared.Paper20261030.ColoredRecordUpdates
import TangoSquared.Paper20261030.ProjectedExecution

/-!
# Cursor operations on the existing record-decorated leaf tree

We reuse `ColoredStorage.Source`, whose leaves carry immutable labels and
whose vertices carry records. Moves, rotations, reads, and writes each
cost one. A write changes the record at the current vertex and preserves
all leaf labels. Erasing records gives the existing `LeafPointer` routing
model; this erasure deliberately makes no assertion about accessing
records after color projection.
-/

namespace TangoSquared.Paper20261030.SourcePointer

open ColoredStorage

variable {α ρ : Type*}

inductive Frame (α ρ : Type*) where
  | left (record : ρ) (right : Source α ρ)
  | right (left : Source α ρ) (record : ρ)

def plug (focus : Source α ρ) : List (Frame α ρ) → Source α ρ
  | [] => focus
  | .left record r :: rest => plug (.fork record focus r) rest
  | .right l record :: rest => plug (.fork record l focus) rest

structure Cursor (α ρ : Type*) where
  focus : Source α ρ
  ancestors : List (Frame α ρ)

def Cursor.tree (c : Cursor α ρ) : Source α ρ := plug c.focus c.ancestors

inductive Step : Cursor α ρ → Cursor α ρ → Prop
  | left (l r : Source α ρ) (record : ρ) (rest) :
      Step ⟨.fork record l r,rest⟩ ⟨l,.left record r :: rest⟩
  | right (l r : Source α ρ) (record : ρ) (rest) :
      Step ⟨.fork record l r,rest⟩ ⟨r,.right l record :: rest⟩
  | upLeft (l r : Source α ρ) (record : ρ) (rest) :
      Step ⟨l,.left record r :: rest⟩ ⟨.fork record l r,rest⟩
  | upRight (l r : Source α ρ) (record : ρ) (rest) :
      Step ⟨r,.right l record :: rest⟩ ⟨.fork record l r,rest⟩
  | rotateRight (u v w : Source α ρ) (p q : ρ) (rest) :
      Step ⟨.fork q (.fork p u v) w,rest⟩ ⟨.fork p u (.fork q v w),rest⟩
  | rotateLeft (u v w : Source α ρ) (p q : ρ) (rest) :
      Step ⟨.fork p u (.fork q v w),rest⟩ ⟨.fork q (.fork p u v) w,rest⟩
  | write (focus : Source α ρ) (fresh : ρ) (rest) :
      Step ⟨focus,rest⟩ ⟨focus.setRoot fresh,rest⟩

inductive Trace : Cursor α ρ → List ρ → Cursor α ρ → Nat → Prop
  | nil (c) : Trace c [] c 0
  | step {c d e reads cost} (move : Step c d) (rest : Trace d reads e cost) :
      Trace c reads e (cost + 1)
  | read {c d reads cost} (rest : Trace c reads d cost) :
      Trace c (c.focus.rootRecord :: reads) d (cost + 1)

theorem Trace.append {c d e : Cursor α ρ} {xs ys : List ρ} {m n : Nat}
    (h : Trace c xs d m) (g : Trace d ys e n) : Trace c (xs ++ ys) e (m + n) := by
  induction h with
  | nil => simpa using g
  | step move rest ih => simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using Trace.step move (ih g)
  | read rest ih => simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using Trace.read (ih g)

def Cursor.extend (c : Cursor α ρ) (outside : List (Frame α ρ)) : Cursor α ρ :=
  ⟨c.focus,c.ancestors ++ outside⟩

theorem Step.extend {c d : Cursor α ρ} (h : Step c d) (outside : List (Frame α ρ)) :
    Step (c.extend outside) (d.extend outside) := by
  cases h
  · exact .left _ _ _ _
  · exact .right _ _ _ _
  · exact .upLeft _ _ _ _
  · exact .upRight _ _ _ _
  · exact .rotateRight _ _ _ _ _ _
  · exact .rotateLeft _ _ _ _ _ _
  · exact .write _ _ _

theorem Trace.extend {c d : Cursor α ρ} {reads : List ρ} {cost : Nat}
    (h : Trace c reads d cost) (outside : List (Frame α ρ)) :
    Trace (c.extend outside) reads (d.extend outside) cost := by
  induction h with
  | nil => exact .nil _
  | step move rest ih => exact .step (move.extend outside) ih
  | read rest ih => exact .read ih

theorem write_charged (focus : Source α ρ) (fresh : ρ) (ancestors) :
    Trace ⟨focus,ancestors⟩ [focus.rootRecord] ⟨focus.setRoot fresh,ancestors⟩ 2 :=
  .read (.step (.write _ _ _) (.nil _))

def frameShape : Frame α ρ → LeafPointer.Frame α
  | .left _ r => .left r.shape
  | .right l _ => .right l.shape

def cursorShape (c : Cursor α ρ) : LeafPointer.Cursor α :=
  ⟨c.focus.shape,c.ancestors.map frameShape⟩

theorem source_nonempty (t : Source α ρ) : t.shape ≠ .empty := by cases t <;> simp [Source.shape]

theorem source_setRoot_shape (t : Source α ρ) (fresh : ρ) :
    (t.setRoot fresh).shape = t.shape := by cases t <;> rfl

theorem cursorShape_tree (c : Cursor α ρ) : (cursorShape c).tree = c.tree.shape := by
  rcases c with ⟨focus,ancestors⟩
  induction ancestors generalizing focus with
  | nil => rfl
  | cons frame rest ih =>
    cases frame with
    | left record r => exact ih (.fork record focus r)
    | right l record => exact ih (.fork record l focus)

theorem Step.routing {c d : Cursor α ρ} (h : Step c d) :
    ∃ cost, LeafPointer.Trace (some (cursorShape c)) (some (cursorShape d)) cost ∧ cost ≤ 1 := by
  cases h with
  | left l r record rest =>
    exact ⟨1,.step (.nav (.left _ _ _ (source_nonempty l))) (.nil _),le_rfl⟩
  | right l r record rest =>
    exact ⟨1,.step (.nav (.right _ _ _ (source_nonempty r))) (.nil _),le_rfl⟩
  | upLeft l r record rest =>
    exact ⟨1,.step (.nav (.upLeft _ _ _ (source_nonempty l))) (.nil _),le_rfl⟩
  | upRight l r record rest =>
    exact ⟨1,.step (.nav (.upRight _ _ _ (source_nonempty r))) (.nil _),le_rfl⟩
  | rotateRight => exact ⟨1,.step (.rotateRight _ _ _ _) (.nil _),le_rfl⟩
  | rotateLeft => exact ⟨1,.step (.rotateLeft _ _ _ _) (.nil _),le_rfl⟩
  | write focus fresh rest =>
    exact ⟨0,by simpa only [cursorShape,source_setRoot_shape] using
      LeafPointer.Trace.nil (some (cursorShape ⟨focus,rest⟩)),by decide⟩

theorem Trace.routing {c d : Cursor α ρ} {reads : List ρ} {cost : Nat}
    (h : Trace c reads d cost) :
    ∃ routingCost, LeafPointer.Trace (some (cursorShape c)) (some (cursorShape d)) routingCost ∧
      routingCost ≤ cost := by
  induction h with
  | nil => exact ⟨0,.nil _,le_rfl⟩
  | step move rest ih =>
    obtain ⟨first,ht,hfirst⟩ := move.routing
    obtain ⟨last,hr,hlast⟩ := ih
    exact ⟨first + last,ht.append hr,by omega⟩
  | read rest ih =>
    obtain ⟨last,hr,hlast⟩ := ih
    exact ⟨last,hr,by omega⟩

theorem plug_leaves_congr {s t : Source α ρ} (h : s.shape.leaves = t.shape.leaves)
    (ancestors : List (Frame α ρ)) :
    (plug s ancestors).shape.leaves = (plug t ancestors).shape.leaves := by
  induction ancestors generalizing s t with
  | nil => exact h
  | cons frame rest ih =>
    cases frame with
    | left record r => exact ih (by simp only [Source.shape,RouterProjection.Router.leaves,h])
    | right l record => exact ih (by simp only [Source.shape,RouterProjection.Router.leaves,h])

theorem Step.leaves {c d : Cursor α ρ} (h : Step c d) : c.tree.shape.leaves = d.tree.shape.leaves := by
  cases h with
  | left | right | upLeft | upRight => rfl
  | rotateRight u v w p q rest =>
    exact plug_leaves_congr (by simp [Source.shape,RouterProjection.Router.leaves,List.append_assoc]) rest
  | rotateLeft u v w p q rest =>
    exact plug_leaves_congr (by simp [Source.shape,RouterProjection.Router.leaves,List.append_assoc]) rest
  | write focus fresh rest =>
    exact plug_leaves_congr (by rw [source_setRoot_shape]) rest

theorem Trace.leaves {c d : Cursor α ρ} {reads : List ρ} {cost : Nat} (h : Trace c reads d cost) :
    c.tree.shape.leaves = d.tree.shape.leaves := by
  induction h with
  | nil => rfl
  | step move rest ih => exact move.leaves.trans ih
  | read rest ih => exact ih

end TangoSquared.Paper20261030.SourcePointer

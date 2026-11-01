import TangoSquared.Paper20261030.Restriction

/-!
# Charged navigation in a fixed leaf restriction

A cursor is a zipper in an actual leaf-oriented tree. After restriction,
an active cursor is at the root of its nonempty projected subtree. When
that subtree disappears, the cursor is parked at the projection of the
nearest ancestor that still contains a retained leaf. If the whole tree
disappears, the projected cursor is absent.
-/

namespace TangoSquared.Paper20261030.LeafPointer

open RouterProjection

variable {α : Type*}

inductive Frame (α : Type*) where
  | left (right : Router α)
  | right (left : Router α)

def plug (focus : Router α) : List (Frame α) → Router α
  | [] => focus
  | .left r :: rest => plug (.fork focus r) rest
  | .right l :: rest => plug (.fork l focus) rest

structure Cursor (α : Type*) where
  focus : Router α
  ancestors : List (Frame α)

def Cursor.tree (c : Cursor α) : Router α := plug c.focus c.ancestors

inductive Move : Cursor α → Cursor α → Prop
  | left (l r : Router α) (rest : List (Frame α)) (hl : l ≠ .empty) :
      Move ⟨.fork l r,rest⟩ ⟨l,.left r :: rest⟩
  | right (l r : Router α) (rest : List (Frame α)) (hr : r ≠ .empty) :
      Move ⟨.fork l r,rest⟩ ⟨r,.right l :: rest⟩
  | upLeft (l r : Router α) (rest : List (Frame α)) (hl : l ≠ .empty) :
      Move ⟨l,.left r :: rest⟩ ⟨.fork l r,rest⟩
  | upRight (l r : Router α) (rest : List (Frame α)) (hr : r ≠ .empty) :
      Move ⟨r,.right l :: rest⟩ ⟨.fork l r,rest⟩

theorem Move.symm {a b : Cursor α} (h : Move a b) : Move b a := by
  cases h with
  | left l r rest hl => exact .upLeft l r rest hl
  | right l r rest hr => exact .upRight l r rest hr
  | upLeft l r rest hl => exact .left l r rest hl
  | upRight l r rest hr => exact .right l r rest hr

theorem Move.tree {a b : Cursor α} (h : Move a b) : a.tree = b.tree := by
  cases h <;> rfl

variable [DecidableEq α]

def projectedFrames (keep : α → Bool) : List (Frame α) → List (Frame α)
  | [] => []
  | .left r :: rest =>
      if r.prune keep = .empty then projectedFrames keep rest
      else .left (r.prune keep) :: projectedFrames keep rest
  | .right l :: rest =>
      if l.prune keep = .empty then projectedFrames keep rest
      else .right (l.prune keep) :: projectedFrames keep rest

def parked (keep : α → Bool) : List (Frame α) → Option (Cursor α)
  | [] => none
  | .left r :: rest =>
      if r.prune keep = .empty then parked keep rest
      else some ⟨r.prune keep,projectedFrames keep rest⟩
  | .right l :: rest =>
      if l.prune keep = .empty then parked keep rest
      else some ⟨l.prune keep,projectedFrames keep rest⟩

def project (keep : α → Bool) (c : Cursor α) : Option (Cursor α) :=
  if c.focus.prune keep = .empty then parked keep c.ancestors
  else some ⟨c.focus.prune keep,projectedFrames keep c.ancestors⟩

/-- Zero or one adjacent moves in an actual projected tree. -/
inductive AtMostOne : Option (Cursor α) → Option (Cursor α) → Prop
  | refl (c) : AtMostOne c c
  | move {a b : Cursor α} (h : Move a b) : AtMostOne (some a) (some b)

theorem AtMostOne.symm {a b : Option (Cursor α)} (h : AtMostOne a b) : AtMostOne b a := by
  cases h with
  | refl => exact .refl _
  | move h => exact .move h.symm

theorem project_left (keep : α → Bool) (l r : Router α) (rest : List (Frame α)) :
    AtMostOne (project keep ⟨.fork l r,rest⟩) (project keep ⟨l,.left r :: rest⟩) := by
  by_cases hl : l.prune keep = .empty
  · by_cases hr : r.prune keep = .empty
    · simp only [project,Router.prune,hl,hr,Router.join,if_pos rfl,parked]
      exact .refl _
    · simp only [project,Router.prune,hl,Router.join,hr,if_false,if_pos rfl,parked]
      exact .refl _
  · by_cases hr : r.prune keep = .empty
    · simp only [project,Router.prune,hr,Router.join_empty,hl,if_false,projectedFrames,if_pos rfl]
      exact .refl _
    · have hj : (l.prune keep).join (r.prune keep) = .fork (l.prune keep) (r.prune keep) := by
        cases he₁ : l.prune keep <;> cases he₂ : r.prune keep <;> simp_all [Router.join]
      simp only [project,Router.prune,hj,reduceCtorEq,if_false,hl,projectedFrames,hr]
      exact .move (.left _ _ _ hl)

theorem project_right (keep : α → Bool) (l r : Router α) (rest : List (Frame α)) :
    AtMostOne (project keep ⟨.fork l r,rest⟩) (project keep ⟨r,.right l :: rest⟩) := by
  by_cases hl : l.prune keep = .empty
  · by_cases hr : r.prune keep = .empty
    · simp only [project,Router.prune,hl,hr,Router.join,if_pos rfl,parked]
      exact .refl _
    · simp only [project,Router.prune,hl,Router.join,hr,if_false,projectedFrames,if_pos rfl]
      exact .refl _
  · by_cases hr : r.prune keep = .empty
    · simp only [project,Router.prune,hr,Router.join_empty,hl,if_false,if_pos rfl,parked]
      exact .refl _
    · have hj : (l.prune keep).join (r.prune keep) = .fork (l.prune keep) (r.prune keep) := by
        cases he₁ : l.prune keep <;> cases he₂ : r.prune keep <;> simp_all [Router.join]
      simp only [project,Router.prune,hj,reduceCtorEq,if_false,hr,projectedFrames,hl]
      exact .move (.right _ _ _ hr)

theorem project_move (keep : α → Bool) {a b : Cursor α} (h : Move a b) :
    AtMostOne (project keep a) (project keep b) := by
  cases h with
  | left l r rest hl => exact project_left keep l r rest
  | right l r rest hr => exact project_right keep l r rest
  | upLeft l r rest hl => exact (project_left keep l r rest).symm
  | upRight l r rest hr => exact (project_right keep l r rest).symm

theorem join_eq_fork {l r : Router α} (hl : l ≠ .empty) (hr : r ≠ .empty) :
    l.join r = .fork l r := by cases l <;> cases r <;> simp_all [Router.join]

theorem prune_plug_congr (keep : α → Bool) {s t : Router α}
    (h : s.prune keep = t.prune keep) (rest : List (Frame α)) :
    (plug s rest).prune keep = (plug t rest).prune keep := by
  induction rest generalizing s t with
  | nil => exact h
  | cons frame rest ih =>
    cases frame with
    | left r => exact ih (by simp only [Router.prune,h])
    | right l => exact ih (by simp only [Router.prune,h])

theorem plug_projectedFrames (keep : α → Bool) (focus : Router α) (rest : List (Frame α))
    (hf : focus.prune keep ≠ .empty) :
    plug (focus.prune keep) (projectedFrames keep rest) = (plug focus rest).prune keep := by
  induction rest generalizing focus with
  | nil => rfl
  | cons frame rest ih =>
    cases frame with
    | left r =>
      by_cases hr : r.prune keep = .empty
      · have hp : (Router.fork focus r).prune keep = focus.prune keep := by
          simp [Router.prune,hr]
        have hh := ih (.fork focus r) (by simpa only [hp] using hf)
        simpa only [projectedFrames,if_pos hr,plug,hp] using hh
      · have hp : (Router.fork focus r).prune keep = .fork (focus.prune keep) (r.prune keep) := by
          exact join_eq_fork hf hr
        have hh := ih (.fork focus r) (by simp [hp])
        simpa only [projectedFrames,if_neg hr,plug,hp] using hh
    | right l =>
      by_cases hl : l.prune keep = .empty
      · have hp : (Router.fork l focus).prune keep = focus.prune keep := by
          simp [Router.prune,hl,Router.join]
        have hh := ih (.fork l focus) (by simpa only [hp] using hf)
        simpa only [projectedFrames,if_pos hl,plug,hp] using hh
      · have hp : (Router.fork l focus).prune keep = .fork (l.prune keep) (focus.prune keep) := by
          exact join_eq_fork hl hf
        have hh := ih (.fork l focus) (by simp [hp])
        simpa only [projectedFrames,if_neg hl,plug,hp] using hh

theorem parked_tree (keep : α → Bool) (rest : List (Frame α)) {d : Cursor α}
    (hd : parked keep rest = some d) : d.tree = (plug .empty rest).prune keep := by
  induction rest with
  | nil => simp [parked] at hd
  | cons frame rest ih =>
    cases frame with
    | left r =>
      by_cases hr : r.prune keep = .empty
      · have hi := ih (by simpa only [parked,if_pos hr] using hd)
        rw [hi]
        exact prune_plug_congr keep (by simp [Router.prune,hr,Router.join]) rest
      · have he : d = ⟨r.prune keep,projectedFrames keep rest⟩ :=
          (Option.some.inj (by simpa only [parked,if_neg hr] using hd)).symm
        rw [he]
        change plug (r.prune keep) (projectedFrames keep rest) = _
        rw [plug_projectedFrames keep r rest hr]
        exact prune_plug_congr keep (by simp [Router.prune,Router.join]) rest
    | right l =>
      by_cases hl : l.prune keep = .empty
      · have hi := ih (by simpa only [parked,if_pos hl] using hd)
        rw [hi]
        exact prune_plug_congr keep (by simp [Router.prune,hl,Router.join]) rest
      · have he : d = ⟨l.prune keep,projectedFrames keep rest⟩ :=
          (Option.some.inj (by simpa only [parked,if_neg hl] using hd)).symm
        rw [he]
        change plug (l.prune keep) (projectedFrames keep rest) = _
        rw [plug_projectedFrames keep l rest hl]
        exact prune_plug_congr keep (by simp [Router.prune]) rest

/-- The active or parked cursor is a cursor in the actual restriction of
the whole source tree, including all its ancestors. -/
theorem project_tree (keep : α → Bool) (c : Cursor α) {d : Cursor α}
    (hd : project keep c = some d) : d.tree = c.tree.prune keep := by
  by_cases hf : c.focus.prune keep = .empty
  · have hp := parked_tree keep c.ancestors (by simpa only [project,if_pos hf] using hd)
    rw [hp]
    exact prune_plug_congr keep (by simpa only [Router.prune] using hf.symm) c.ancestors
  · have he : d = ⟨c.focus.prune keep,projectedFrames keep c.ancestors⟩ :=
      (Option.some.inj (by simpa only [project,if_neg hf] using hd)).symm
    rw [he]
    exact plug_projectedFrames keep c.focus c.ancestors hf

end TangoSquared.Paper20261030.LeafPointer

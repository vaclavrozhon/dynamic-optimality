import ChaCha.Paper20261030.ProjectedNavigation

/-!
# Projection of complete one-cursor routing executions

Steps are actual adjacent moves and rotations of a leaf-oriented tree.
Restriction maps each step to zero or one such steps and maps a complete
execution to one with no greater cost. The absent option represents a
color that has no leaves in the whole component, and admits no steps.
Record updates and additional simultaneous cursors remain separate from
this routing theorem.
-/

namespace ChaCha.Paper20261030.LeafPointer

open RouterProjection

variable {α : Type*}

inductive Step : Cursor α → Cursor α → Prop
  | nav {c d : Cursor α} (move : Move c d) : Step c d
  | rotateRight (u v w : Router α) (rest : List (Frame α)) :
      Step ⟨.fork (.fork u v) w,rest⟩ ⟨.fork u (.fork v w),rest⟩
  | rotateLeft (u v w : Router α) (rest : List (Frame α)) :
      Step ⟨.fork u (.fork v w),rest⟩ ⟨.fork (.fork u v) w,rest⟩

inductive Trace : Option (Cursor α) → Option (Cursor α) → Nat → Prop
  | nil (c) : Trace c c 0
  | step {c d : Cursor α} {e : Option (Cursor α)} {cost : Nat}
      (move : Step c d) (rest : Trace (some d) e cost) : Trace (some c) e (cost + 1)

theorem Trace.append {a b c : Option (Cursor α)} {m n : Nat}
    (h : Trace a b m) (g : Trace b c n) : Trace a c (m + n) := by
  induction h with
  | nil => simpa using g
  | step move rest ih =>
    simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using Trace.step move (ih g)

theorem AtMostOne.trace {a b : Option (Cursor α)} (h : AtMostOne a b) :
    ∃ cost, Trace a b cost ∧ cost ≤ 1 := by
  cases h with
  | refl => exact ⟨0,.nil _,by decide⟩
  | move h => exact ⟨1,.step (.nav h) (.nil _),le_rfl⟩

variable [DecidableEq α]

theorem project_rotate_right (keep : α → Bool) (u v w : Router α) (rest : List (Frame α)) :
    ∃ cost, Trace (project keep ⟨.fork (.fork u v) w,rest⟩)
      (project keep ⟨.fork u (.fork v w),rest⟩) cost ∧ cost ≤ 1 := by
  simp only [project,Router.prune]
  generalize u.prune keep = up
  generalize v.prune keep = vp
  generalize w.prune keep = wp
  cases up <;> cases vp <;> cases wp <;>
    simp only [Router.join,reduceCtorEq,if_true,if_false]
  all_goals first
    | exact ⟨0,.nil _,by decide⟩
    | exact ⟨1,.step (.rotateRight _ _ _ _) (.nil _),le_rfl⟩

theorem project_rotate_left (keep : α → Bool) (u v w : Router α) (rest : List (Frame α)) :
    ∃ cost, Trace (project keep ⟨.fork u (.fork v w),rest⟩)
      (project keep ⟨.fork (.fork u v) w,rest⟩) cost ∧ cost ≤ 1 := by
  simp only [project,Router.prune]
  generalize u.prune keep = up
  generalize v.prune keep = vp
  generalize w.prune keep = wp
  cases up <;> cases vp <;> cases wp <;>
    simp only [Router.join,reduceCtorEq,if_true,if_false]
  all_goals first
    | exact ⟨0,.nil _,by decide⟩
    | exact ⟨1,.step (.rotateLeft _ _ _ _) (.nil _),le_rfl⟩

theorem project_step (keep : α → Bool) {a b : Cursor α} (h : Step a b) :
    ∃ cost, Trace (project keep a) (project keep b) cost ∧ cost ≤ 1 := by
  cases h with
  | nav move => exact (project_move keep move).trace
  | rotateRight u v w rest => exact project_rotate_right keep u v w rest
  | rotateLeft u v w rest => exact project_rotate_left keep u v w rest

def projectOptional (keep : α → Bool) (c : Option (Cursor α)) : Option (Cursor α) :=
  c.bind (project keep)

theorem project_trace (keep : α → Bool) {a b : Option (Cursor α)} {cost : Nat}
    (h : Trace a b cost) :
    ∃ projectedCost, Trace (projectOptional keep a) (projectOptional keep b) projectedCost ∧
      projectedCost ≤ cost := by
  induction h with
  | nil c => exact ⟨0,.nil _,le_rfl⟩
  | step move rest ih =>
    obtain ⟨first,ht,hfirst⟩ := project_step keep move
    obtain ⟨last,hr,hlast⟩ := ih
    refine ⟨first + last,?_,by omega⟩
    exact ht.append hr

end ChaCha.Paper20261030.LeafPointer

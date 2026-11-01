import Splay.Accounting.OfflineSupportedPath

namespace Splay.Accounting.OfflineConnectedSupport.SupportedPath

open Splay.Tree.BST
open Splay.Accounting.OfflineNormalForm

/-- The actual intermediate tree at each time of the data-valued path. -/
def state {lower upper : ℕ} {before after : BST lower upper}
    {a : RootPrefix before} {b : RootPrefix after} (path : SupportedPath a b) :
    Fin (path.length + 1) → BST lower upper :=
  match path with
  | .nil _ => fun _ => before
  | .cons _ _ tail => Fin.cons before tail.state

def rotationDepth {lower upper : ℕ} {before after : BST lower upper}
    {a : RootPrefix before} {b : RootPrefix after} (path : SupportedPath a b) :
    Fin path.length → ℕ :=
  match path with
  | .nil _ => Fin.elim0
  | @cons depth _ _ _ _ _ _ _ _ _ _ tail => Fin.cons depth tail.rotationDepth

@[simp] theorem state_zero {lower upper : ℕ} {before after : BST lower upper}
    {a : RootPrefix before} {b : RootPrefix after} (path : SupportedPath a b) :
    path.state 0 = before := by
  cases path <;> simp [state]

@[simp] theorem state_last {lower upper : ℕ} {before after : BST lower upper}
    {a : RootPrefix before} {b : RootPrefix after} (path : SupportedPath a b) :
    path.state (Fin.last path.length) = after := by
  induction path with
  | nil => rfl
  | cons rotation supported tail ih => simpa [state, length] using ih

theorem rotates {lower upper : ℕ} {before after : BST lower upper}
    {a : RootPrefix before} {b : RootPrefix after} (path : SupportedPath a b)
    (step : Fin path.length) :
    RotationAt (path.rotationDepth step)
      (path.state step.castSucc) (path.state step.succ) := by
  induction path with
  | nil => exact Fin.elim0 step
  | cons rotation supported tail ih =>
      refine Fin.cases ?_ (fun next => ?_) step
      · simpa [state, rotationDepth, length] using rotation
      · simpa [state, rotationDepth, length] using ih next

theorem forallTrees_iff {lower upper : ℕ} {before after : BST lower upper}
    {a : RootPrefix before} {b : RootPrefix after} (path : SupportedPath a b)
    (property : BST lower upper → Prop) :
    path.ForallTrees property ↔ ∀ time, property (path.state time) := by
  induction path with
  | nil => exact ⟨fun all _ => all, fun all => all 0⟩
  | cons rotation supported tail ih =>
      constructor
      · rintro ⟨first, rest⟩ time
        refine Fin.cases ?_ (fun next => ?_) time
        · simpa [state] using first
        · simpa [state, length] using (ih property).mp rest next
      · intro all
        refine ⟨by simpa only [state_zero] using all 0, (ih property).mpr ?_⟩
        intro time
        simpa [state, length] using all time.succ

theorem depthBound_iff {lower upper bound : ℕ} {before after : BST lower upper}
    {a : RootPrefix before} {b : RootPrefix after} (path : SupportedPath a b) :
    path.DepthBound bound ↔ ∀ step, path.rotationDepth step ≤ bound := by
  induction path with
  | nil => exact ⟨fun _ step => Fin.elim0 step, fun _ => trivial⟩
  | cons rotation supported tail ih =>
      constructor
      · rintro ⟨first, rest⟩ step
        refine Fin.cases ?_ (fun next => ?_) step
        · simpa [rotationDepth] using first
        · simpa [rotationDepth] using ih.mp rest next
      · intro all
        refine ⟨by simpa [rotationDepth, length] using all ⟨0, by simp [length]⟩, ih.mpr ?_⟩
        intro step
        simpa [rotationDepth] using all step.succ

theorem visits_iff {lower upper key : ℕ} {before after : BST lower upper}
    {a : RootPrefix before} {b : RootPrefix after} (path : SupportedPath a b) :
    path.Visits key ↔ ∃ time, (path.state time).HasRoot key := by
  induction path with
  | nil => exact ⟨fun root => ⟨0, root⟩, fun ⟨_, root⟩ => root⟩
  | cons rotation supported tail ih =>
      constructor
      · rintro (first | rest)
        · exact ⟨0, by simpa [state] using first⟩
        · obtain ⟨time, root⟩ := ih.mp rest
          exact ⟨time.succ, by simpa [state, length] using root⟩
      · rintro ⟨time, root⟩
        revert root
        refine Fin.cases ?_ (fun next => ?_) time
        · intro root
          exact .inl (by simpa [state] using root)
        · intro root
          exact .inr (ih.mpr ⟨next, by simpa [state] using root⟩)

/-- The path can be exported without re-choosing any of its states. -/
def toExactTraceNil {n : ℕ} {before after : BST 0 n}
    {a : RootPrefix before} {b : RootPrefix after} (path : SupportedPath a b) :
    ExactTrace [] before after path.length where
  state := path.state
  rotationDepth := path.rotationDepth
  rotates := path.rotates
  servedAt := Fin.elim0
  servedInOrder := fun request => Fin.elim0 request
  serves := fun request => Fin.elim0 request
  initial_eq := path.state_zero
  final_eq := path.state_last

/-- Serve a selected key at its certified visit, with the same exact states. -/
noncomputable def toExactTraceSingleton {n : ℕ} {before after : BST 0 n}
    {a : RootPrefix before} {b : RootPrefix after} (path : SupportedPath a b)
    (key : Fin n) (visit : path.Visits key.val) :
    ExactTrace [key] before after path.length where
  state := path.state
  rotationDepth := path.rotationDepth
  rotates := path.rotates
  servedAt := fun _ => Classical.choose (path.visits_iff.mp visit)
  servedInOrder := fun _ _ _ => le_rfl
  serves := by
    intro request
    have root := Classical.choose_spec (path.visits_iff.mp visit)
    simpa using root
  initial_eq := path.state_zero
  final_eq := path.state_last

end Splay.Accounting.OfflineConnectedSupport.SupportedPath

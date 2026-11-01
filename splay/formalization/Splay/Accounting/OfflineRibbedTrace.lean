import Splay.Accounting.OfflineBoundedTrace
import Splay.Accounting.OfflineRestrictedMacros

namespace Splay.Accounting.OfflineNormalForm

open Splay.Tree.BST

/-- A physical trace retaining bounded ribs at every intermediate state. -/
inductive RibbedTrace {n : ℕ} (height depthBound slack : ℕ) :
    List (Fin n) → BST 0 n → BST 0 n → ℕ → Prop
  | done (tree : BST 0 n) (height_le : tree.height ≤ height) (ribs : HasBoundedMinorRibs tree slack) :
      RibbedTrace height depthBound slack [] tree tree 0
  | rotate {accesses : List (Fin n)} {before middle after : BST 0 n} {depth rotations : ℕ}
      (rotation : RotationAt depth before middle) (depth_le : depth ≤ depthBound)
      (height_le : before.height ≤ height) (ribs : HasBoundedMinorRibs before slack)
      (tail : RibbedTrace height depthBound slack accesses middle after rotations) :
      RibbedTrace height depthBound slack accesses before after (rotations + 1)
  | serve {access : Fin n} {accesses : List (Fin n)} {before after : BST 0 n} {rotations : ℕ}
      (root : before.HasRoot access.val)
      (tail : RibbedTrace height depthBound slack accesses before after rotations) :
      RibbedTrace height depthBound slack (access :: accesses) before after rotations

namespace RibbedTrace

theorem append {n height depth slack r₁ r₂ : ℕ} {xs ys : List (Fin n)} {a b c : BST 0 n}
    (first : RibbedTrace height depth slack xs a b r₁) (second : RibbedTrace height depth slack ys b c r₂) :
    RibbedTrace height depth slack (xs ++ ys) a c (r₁ + r₂) := by
  induction first with
  | done => simpa using second
  | rotate rotation depth_le height_le ribs tail ih =>
      simpa [Nat.add_right_comm] using RibbedTrace.rotate rotation depth_le height_le ribs (ih second)
  | serve root tail ih => exact .serve root (ih second)

theorem exists_exactTrace {n height depth slack rotations : ℕ} {xs : List (Fin n)} {a b : BST 0 n}
    (trace : RibbedTrace height depth slack xs a b rotations) :
    ∃ result : ExactTrace xs a b rotations,
      (∀ time, (result.state time).height ≤ height) ∧ (∀ step, result.rotationDepth step ≤ depth) ∧
      (∀ time, HasBoundedMinorRibs (result.state time) slack) := by
  induction trace with
  | done tree bounded ribs =>
      exact ⟨⟨fun _ => tree, Fin.elim0, fun step => Fin.elim0 step,
        Fin.elim0, fun request => Fin.elim0 request, fun request => Fin.elim0 request,
        rfl, rfl⟩, fun _ => bounded, fun step => Fin.elim0 step, fun _ => ribs⟩
  | @rotate accesses before middle after d rotations rotation dBound hBound ribs tail ih =>
      obtain ⟨result, heights, depths, ribBounds⟩ := ih
      let next : ExactTrace accesses before after (rotations + 1) :=
        { state := Fin.cons before result.state
          rotationDepth := Fin.cons d result.rotationDepth
          rotates := fun step => Fin.cases (by simpa [result.initial_eq] using rotation)
            (fun i => by simpa using result.rotates i) step
          servedAt := fun request => (result.servedAt request).succ
          servedInOrder := fun i j h => by
            exact Fin.le_iff_val_le_val.mpr (Nat.add_le_add_right
              (Fin.le_iff_val_le_val.mp (result.servedInOrder h)) 1)
          serves := fun request => by simpa using result.serves request
          initial_eq := by simp
          final_eq := by simpa using result.final_eq }
      refine ⟨next, ?_, ?_, ?_⟩
      · intro time
        exact Fin.cases (by simpa [next] using hBound) (fun i => by simpa [next] using heights i) time
      · intro step
        exact Fin.cases (by simpa [next] using dBound) (fun i => by simpa [next] using depths i) step
      · intro time
        exact Fin.cases (by simpa [next] using ribs) (fun i => by simpa [next] using ribBounds i) time
  | @serve access accesses before after rotations root tail ih =>
      obtain ⟨result, heights, depths, ribBounds⟩ := ih
      let next : ExactTrace (access :: accesses) before after rotations :=
        { result with
          servedAt := Fin.cases 0 result.servedAt
          servedInOrder := by
            intro i
            refine Fin.cases (by intro j h; exact Fin.zero_le _) (fun i => ?_) i
            intro j
            refine Fin.cases ?_ (fun j => ?_) j
            · intro ordered
              simp at ordered
            · intro ordered
              exact result.servedInOrder (by simpa using ordered)
          serves := fun request => Fin.cases (by simpa [result.initial_eq] using root)
            (fun i => by simpa using result.serves i) request }
      exact ⟨next, heights, depths, ribBounds⟩

end RibbedTrace

theorem BoundedTrace.initial_height {n height depth rotations : ℕ} {xs : List (Fin n)} {a b : BST 0 n}
    (trace : BoundedTrace height depth xs a b rotations) : a.height ≤ height := by
  induction trace with
  | done tree bound => exact bound
  | rotate rotation depth bound tail ih => exact bound
  | serve root tail ih => exact ih

end Splay.Accounting.OfflineNormalForm

namespace Splay.Accounting.OfflineConnectedSupport

open OfflineNormalForm

theorem SupportedPath.toRibbedTraceNil {n height depth slack : ℕ} {before after : BST 0 n}
    {a : RootPrefix before} {b : RootPrefix after} (path : SupportedPath a b)
    (heights : path.ForallTrees (fun tree => tree.height ≤ height)) (depths : path.DepthBound depth)
    (ribs : path.ForallTrees (fun tree => HasBoundedMinorRibs tree slack)) :
    RibbedTrace height depth slack [] before after path.length := by
  generalize lengthEq : path.length = count
  induction count using Nat.strong_induction_on generalizing before after with
  | h count ih =>
      cases path with
      | nil => rw [← lengthEq]; exact .done _ heights ribs
      | cons rotation supported tail =>
          have rest := ih tail.length (by simp only [SupportedPath.length] at lengthEq; omega)
            tail heights.2 depths.2 ribs.2 rfl
          rw [← lengthEq]
          exact .rotate rotation depths.1 heights.1 ribs.1 rest

theorem HasSupportedPath.exists_ribbedTrace {n support rotations height slack : ℕ}
    {before after : BST 0 n} (execution : HasSupportedPath before after support rotations)
    (endpoints : max before.height after.height + support ≤ height)
    (beforeRibs : HasBoundedMinorRibs before slack) (afterRibs : HasBoundedMinorRibs after slack) :
    ∃ count, RibbedTrace height 1 (slack + 1) [] before after count ∧ count ≤ 4 * support := by
  obtain ⟨a, b, path, card, _⟩ := execution
  by_cases positive : 0 < a.card
  · obtain ⟨result, cost, depth, heights, ribs, _⟩ :=
      exists_restrictedPath_of_sameFrontier a b path.toExecution.frontier_eq positive beforeRibs afterRibs
    exact ⟨result.length, result.toRibbedTraceNil (heights.imp (fun _ bound => by omega)) depth ribs, by omega⟩
  · have same := path.eq_of_card_zero (by omega)
    subst after
    exact ⟨0, .done _ (by omega) (beforeRibs.mono (by omega)), by omega⟩

end Splay.Accounting.OfflineConnectedSupport

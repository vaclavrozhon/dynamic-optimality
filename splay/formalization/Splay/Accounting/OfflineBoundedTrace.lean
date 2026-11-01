import Splay.Accounting.OfflineSupportedTrace

namespace Splay.Accounting.OfflineNormalForm

open Splay.Tree.BST

/-- A construction-oriented trace whose bounds cover every actual state and
rotation, including states at repeated or zero-cost requests. -/
inductive BoundedTrace {n : ℕ} (height depthBound : ℕ) :
    List (Fin n) → BST 0 n → BST 0 n → ℕ → Prop
  | done (tree : BST 0 n) (height_le : tree.height ≤ height) :
      BoundedTrace height depthBound [] tree tree 0
  | rotate {accesses : List (Fin n)} {before middle after : BST 0 n} {depth rotations : ℕ}
      (rotation : RotationAt depth before middle) (depth_le : depth ≤ depthBound)
      (height_le : before.height ≤ height)
      (tail : BoundedTrace height depthBound accesses middle after rotations) :
      BoundedTrace height depthBound accesses before after (rotations + 1)
  | serve {access : Fin n} {accesses : List (Fin n)} {before after : BST 0 n} {rotations : ℕ}
      (root : before.HasRoot access.val)
      (tail : BoundedTrace height depthBound accesses before after rotations) :
      BoundedTrace height depthBound (access :: accesses) before after rotations

namespace BoundedTrace

theorem append {n height depth r₁ r₂ : ℕ} {xs ys : List (Fin n)} {a b c : BST 0 n}
    (first : BoundedTrace height depth xs a b r₁) (second : BoundedTrace height depth ys b c r₂) :
    BoundedTrace height depth (xs ++ ys) a c (r₁ + r₂) := by
  induction first with
  | done => simpa using second
  | rotate rotation depth_le height_le tail ih =>
      simpa [Nat.add_right_comm] using BoundedTrace.rotate rotation depth_le height_le (ih second)
  | serve root tail ih => exact .serve root (ih second)

theorem mono {n height depth height' depth' rotations : ℕ} {xs : List (Fin n)} {a b : BST 0 n}
    (trace : BoundedTrace height depth xs a b rotations)
    (height_le : height ≤ height') (depth_le : depth ≤ depth') :
    BoundedTrace height' depth' xs a b rotations := by
  induction trace with
  | done tree bounded => exact .done tree (bounded.trans height_le)
  | rotate rotation bounded height tail ih =>
      exact .rotate rotation (bounded.trans depth_le) (height.trans height_le) ih
  | serve root tail ih => exact .serve root ih

/-- Export all geometric invariants together with the very same indexed trace. -/
theorem exists_exactTrace {n height depth rotations : ℕ} {xs : List (Fin n)} {a b : BST 0 n}
    (trace : BoundedTrace height depth xs a b rotations) :
    ∃ result : ExactTrace xs a b rotations,
      (∀ time, (result.state time).height ≤ height) ∧
      (∀ step, result.rotationDepth step ≤ depth) := by
  induction trace with
  | done tree bounded =>
      exact ⟨⟨fun _ => tree, Fin.elim0, fun step => Fin.elim0 step,
        Fin.elim0, fun request => Fin.elim0 request, fun request => Fin.elim0 request,
        rfl, rfl⟩, fun _ => bounded, fun step => Fin.elim0 step⟩
  | @rotate accesses before middle after d rotations rotation dBound hBound tail ih =>
      obtain ⟨result, heights, depths⟩ := ih
      let next : ExactTrace accesses before after (rotations + 1) :=
        { state := Fin.cons before result.state
          rotationDepth := Fin.cons d result.rotationDepth
          rotates := fun step => Fin.cases
            (by simpa [result.initial_eq] using rotation)
            (fun i => by simpa using result.rotates i) step
          servedAt := fun request => (result.servedAt request).succ
          servedInOrder := fun i j h => by
            exact Fin.le_iff_val_le_val.mpr (Nat.add_le_add_right
              (Fin.le_iff_val_le_val.mp (result.servedInOrder h)) 1)
          serves := fun request => by simpa using result.serves request
          initial_eq := by simp
          final_eq := by simpa using result.final_eq }
      refine ⟨next, ?_, ?_⟩
      · intro time
        exact Fin.cases (by simpa [next] using hBound)
          (fun i => by simpa [next] using heights i) time
      · intro step
        exact Fin.cases (by simpa [next] using dBound)
          (fun i => by simpa [next] using depths i) step
  | @serve access accesses before after rotations root tail ih =>
      obtain ⟨result, heights, depths⟩ := ih
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
          serves := fun request => Fin.cases
            (by simpa [result.initial_eq] using root)
            (fun i => by simpa using result.serves i) request }
      exact ⟨next, heights, depths⟩

end BoundedTrace

end Splay.Accounting.OfflineNormalForm

namespace Splay.Accounting.OfflineConnectedSupport.SupportedPath

open OfflineNormalForm

theorem toBoundedTraceNil {n height depth : ℕ} {before after : BST 0 n}
    {a : RootPrefix before} {b : RootPrefix after} (path : SupportedPath a b)
    (heights : path.ForallTrees (fun tree => tree.height ≤ height)) (depths : path.DepthBound depth) :
    BoundedTrace height depth [] before after path.length := by
  generalize lengthEq : path.length = count
  induction count using Nat.strong_induction_on generalizing before after with
  | h count ih =>
      cases path with
      | nil => rw [← lengthEq]; exact .done _ heights
      | cons rotation supported tail =>
          have rest := ih tail.length (by simp only [length] at lengthEq; omega) tail heights.2 depths.2 rfl
          rw [← lengthEq]
          exact .rotate rotation depths.1 heights.1 rest

theorem toBoundedTraceSingleton {n height depth : ℕ} {before after : BST 0 n}
    {a : RootPrefix before} {b : RootPrefix after} (path : SupportedPath a b)
    (heights : path.ForallTrees (fun tree => tree.height ≤ height)) (depths : path.DepthBound depth)
    (key : Fin n) (visit : path.Visits key.val) :
    BoundedTrace height depth [key] before after path.length := by
  generalize lengthEq : path.length = count
  induction count using Nat.strong_induction_on generalizing before after with
  | h count ih =>
      cases path with
      | nil => rw [← lengthEq]; exact .serve visit (.done _ heights)
      | cons rotation supported tail =>
          rcases visit with root | visit
          · rw [← lengthEq]
            exact .serve root (.rotate rotation depths.1 heights.1 (tail.toBoundedTraceNil heights.2 depths.2))
          · have rest := ih tail.length (by simp only [length] at lengthEq; omega) tail heights.2 depths.2 visit rfl
            rw [← lengthEq]
            exact .rotate rotation depths.1 heights.1 rest

end Splay.Accounting.OfflineConnectedSupport.SupportedPath

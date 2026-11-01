import Splay.Accounting.OfflineRestrictedRotations
import Splay.Accounting.OfflineSupportedTrace

namespace Splay.Accounting.OfflineConnectedSupport

open Splay.Assumptions.NormalForm
open OfflineNormalForm

theorem RootPrefix.mem_keys_of_hasRoot {lower upper key : ℕ}
    {tree : BST lower upper} (selected : RootPrefix tree)
    (positive : 0 < selected.card) (root : tree.HasRoot key) : key ∈ selected.keys := by
  cases selected with
  | none => simp [RootPrefix.card] at positive
  | node left right =>
      obtain ⟨_, _, equal⟩ := root
      cases equal
      simp [RootPrefix.keys]

/-- Export the restricted conversion as the existing exact comparison trace,
serving one requested selected key at its certified intermediate root visit. -/
theorem exists_restrictedTrace_of_sameFrontier
    {n slack : ℕ} {before after : BST 0 n}
    (a : RootPrefix before) (b : RootPrefix after)
    (same : a.frontier = b.frontier) (positive : 0 < a.card)
    (beforeRibs : HasBoundedMinorRibs before slack)
    (afterRibs : HasBoundedMinorRibs after slack)
    (key : Fin n) (selectedKey : key.val ∈ a.keys) :
    ∃ (rotations : ℕ) (trace : ExactTrace [key] before after rotations),
      rotations + 4 ≤ 4 * a.card ∧
      (∀ step, trace.rotationDepth step ≤ 1) ∧
      (∀ time, (trace.state time).height ≤ max before.height after.height + a.card) ∧
      (∀ time, HasBoundedMinorRibs (trace.state time) (slack + 1)) := by
  obtain ⟨path, cost, depths, heights, ribs, visits⟩ :=
    exists_restrictedPath_of_sameFrontier a b same positive beforeRibs afterRibs
  exact ⟨path.length, path.toExactTraceSingleton key (visits key.val selectedKey),
    cost, path.depthBound_iff.mp depths, path.forallTrees_iff _ |>.mp heights,
    path.forallTrees_iff _ |>.mp ribs⟩

/-- A connected service is replaced as one macro, preserving its exact
endpoints. The original supported rotation count need not be preserved. -/
theorem SupportedRotationExecution.exists_restrictedTrace_serving
    {n rotations slack : ℕ} {before after : BST 0 n}
    {a : RootPrefix before} {b : RootPrefix after}
    (execution : SupportedRotationExecution rotations a b)
    (positive : 0 < a.card) (key : Fin n) (served : after.HasRoot key.val)
    (beforeRibs : HasBoundedMinorRibs before slack)
    (afterRibs : HasBoundedMinorRibs after slack) :
    ∃ (targetRotations : ℕ) (trace : ExactTrace [key] before after targetRotations),
      targetRotations + 4 ≤ 4 * a.card ∧
      (∀ step, trace.rotationDepth step ≤ 1) ∧
      (∀ time, (trace.state time).height ≤ max before.height after.height + a.card) ∧
      (∀ time, HasBoundedMinorRibs (trace.state time) (slack + 1)) := by
  apply exists_restrictedTrace_of_sameFrontier a b execution.frontier_eq positive beforeRibs afterRibs key
  rw [execution.keys_eq]
  exact b.mem_keys_of_hasRoot (by have := execution.card_eq; omega) served

end Splay.Accounting.OfflineConnectedSupport

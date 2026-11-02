import DynamicOptimality.SearchRotationModel

/-!
# Restoring arbitrary hanging components

The split-tree kernels operate on one class of equal last-touch time. Their
external gaps may contain entire older classes. Every ordinary rotation
of a class skeleton lifts, with the same count, after all those subtrees
are restored in their unchanged inorder slots.
-/

namespace DynamicOptimality.GeometricOnlineSimulation

open ChaCha.MTR SearchRotation

variable {α : Type*}

theorem rotation_inorder {before after : RawTree α} (step : Rotation before after) :
    before.inorder = after.inorder := by
  induction step with
  | rootRight => simp [Tree.inorder, List.append_assoc]
  | rootLeft => simp [Tree.inorder, List.append_assoc]
  | leftContext step key right ih => simp only [Tree.inorder, ih]
  | rightContext left key step ih => simp only [Tree.inorder, ih]

theorem rotation_size {before after : RawTree α} (step : Rotation before after) :
    before.size = after.size := by
  simpa only [Tree.length_inorder] using congrArg List.length (rotation_inorder step)

theorem rotation_graft {before after : RawTree α} (step : Rotation before after)
    (gaps : Nat → RawTree α) (start : Nat) :
    Rotation (Tree.graft before gaps start) (Tree.graft after gaps start) := by
  induction step generalizing start with
  | rootRight a b c x y =>
      simpa only [Tree.graft, Tree.size, Nat.add_assoc] using
        Rotation.rootRight (Tree.graft a gaps start) (Tree.graft b gaps (start + a.size + 1))
          (Tree.graft c gaps (start + a.size + 1 + b.size + 1)) x y
  | rootLeft a b c x y =>
      simpa only [Tree.graft, Tree.size, Nat.add_assoc] using
        Rotation.rootLeft (Tree.graft a gaps start) (Tree.graft b gaps (start + a.size + 1))
          (Tree.graft c gaps (start + a.size + 1 + b.size + 1)) x y
  | leftContext step key right ih =>
      simp only [Tree.graft, rotation_size step]
      exact .leftContext (ih start) _ _
  | rightContext left key step ih =>
      exact .rightContext _ _ (ih (start + left.size + 1))

theorem rotations_graft {before after : RawTree α} {count : Nat}
    (run : Rotations before after count) (gaps : Nat → RawTree α) (start : Nat := 0) :
    Rotations (Tree.graft before gaps start) (Tree.graft after gaps start) count := by
  induction run with
  | refl => exact .refl _
  | step first rest ih => exact .step (rotation_graft first gaps start) ih

end DynamicOptimality.GeometricOnlineSimulation

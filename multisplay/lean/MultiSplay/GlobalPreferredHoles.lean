import MultiSplay.GlobalMarkedSwitchReflection

/-!
# Ordered foreign subtrees under preferred-component rotations

The skeleton and physical tree determine a marked component uniquely.
Rotating its skeleton preserves the complete inorder list of foreign
subtrees. These are the attachment facts needed to carry a recursive
global representation through the local classical switch.
-/

namespace MultiSplay.Global

open DynamicOptimality DynamicOptimality.SearchRotation
open ChaCha.MTR
open Pointer (MarkedTree)

variable {α : Type*}

theorem marked_ext {before after : MarkedTree α}
    (skeleton : before.skeleton = after.skeleton)
    (physical : before.erase = after.erase) : before = after := by
  induction before generalizing after with
  | hole tree =>
      cases after <;> simp_all [MarkedTree.skeleton, MarkedTree.erase]
  | node left key right ihLeft ihRight =>
      cases after with
      | hole tree => simp [MarkedTree.skeleton] at skeleton
      | node left' key' right' =>
          simp only [MarkedTree.skeleton, Tree.node.injEq] at skeleton
          simp only [MarkedTree.erase, Tree.node.injEq] at physical
          rcases skeleton with ⟨leftSkeleton, keyEq, rightSkeleton⟩
          rcases physical with ⟨leftPhysical, _, rightPhysical⟩
          subst key'
          rw [ihLeft leftSkeleton leftPhysical, ihRight rightSkeleton rightPhysical]

@[simp] theorem markedGraft_gapArray (before : MarkedTree α) :
    markedGraft before.skeleton before.gapArray 0 = before := by
  apply marked_ext
  · exact markedGraft_skeleton _ _ _
  · simpa only [markedGraft_erase] using before.graft_gapArray

theorem rotation_holes {before after : RawTree α} (step : Rotation before after)
    (gaps : Nat → RawTree α) (start : Nat) :
    (markedGraft before gaps start).holes = (markedGraft after gaps start).holes := by
  induction step generalizing start with
  | rootRight a x b y c =>
      simp [markedGraft, MarkedTree.holes, Tree.size, List.append_assoc,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  | rootLeft a x b y c =>
      simp [markedGraft, MarkedTree.holes, Tree.size, List.append_assoc,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  | leftContext step key right ih =>
      simp only [markedGraft, MarkedTree.holes, ih, rotation_size step]
  | rightContext left key step ih =>
      simp only [markedGraft, MarkedTree.holes, ih]

theorem rotations_holes {before after : RawTree α} {count : Nat}
    (run : Rotations before after count) (gaps : Nat → RawTree α) (start : Nat) :
    (markedGraft before gaps start).holes = (markedGraft after gaps start).holes := by
  induction run with
  | refl tree => rfl
  | step first rest ih => exact (rotation_holes first gaps start).trans ih

end MultiSplay.Global

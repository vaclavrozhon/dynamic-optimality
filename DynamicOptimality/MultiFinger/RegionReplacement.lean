import DynamicOptimality.MultiFinger.RegionReplacementExpose
import DynamicOptimality.GeometricOnlineSimulation.Linearize

/-!
# Constant-size region replacement in the physical top tree

Two boundary splays expose the region. At most eighteen rotations match
its old marked shape, after which the supplied physical rotation sequence
is executed literally. Replacing at most three marks changes the internal
potential by at most three and changes at most two ancestor ranks.
-/

namespace DynamicOptimality.MultiFinger

open ChaCha.MTR
open Pointer (MarkedTree)
open SearchRotation
open ChaCha.Paper20261030.SplayAuxiliary (potential)

namespace Top

theorem rotations_context {α : Type*} (context : MarkedTree.Context α)
    {before after : MarkedTree α} {count : Nat}
    (run : Rotations before.erase after.erase count) :
    Rotations (context.plug before).erase (context.plug after).erase count := by
  induction context with
  | top => exact run
  | left parent right inside ih =>
      exact ih.plug [.left parent right.erase]
  | right left parent inside ih =>
      exact ih.plug [.right left.erase parent]

end Top

/-- The specification is discharged by ordinary rotations, with a uniform
constant. The surrounding markers and every outside hole remain exact. -/
theorem regionReplacementBound : RegionReplacementBound 32 := by
  intro frame before oldBlock newBlock rawCount capacity contained ordered _newUnique
    fits oldSmall newSmall raw
  have skeletonOrdered : before.skeleton.Ordered := ordered.sublist (Top.skeleton_sublist before)
  obtain ⟨context, block, exposedCount, matching, shallow, blockKeys, blockHoles,
    exposeRun, exposeBound⟩ := RegionFrame.expose frame before oldBlock contained skeletonOrdered fits
  have blockSize : block.skeleton.size = oldBlock.skeleton.size := by
    simpa only [Tree.length_inorder] using congrArg List.length blockKeys
  have unchangedKeys : (context.plug block).skeleton.inorder = before.skeleton.inorder := by
    rw [MarkedTree.Context.keys_plug, matching.1, matching.2.1, blockKeys]
    exact contained.1.symm
  have unchangedSize : (context.plug block).skeleton.size = before.skeleton.size := by
    simpa only [Tree.length_inorder] using congrArg List.length unchangedKeys
  obtain ⟨shapeCount, shapeBound, shapeRun⟩ :=
    GeometricOnlineSimulation.marked_rotations block oldBlock blockHoles blockKeys
  have newPotential : potential newBlock.skeleton ≤ 3 := by
    have bound := ChaCha.Paper20261030.SplayAuxiliary.potential_le newBlock.skeleton 3 newSmall
    have logarithm : Nat.log 2 3 = 1 := by decide
    rw [logarithm, Nat.mul_one] at bound
    exact bound.trans newSmall
  have finalFits : (context.plug newBlock).skeleton.size ≤ capacity + 4 := by
    have difference := Top.context_size_difference context block newBlock
    rw [unchangedSize] at difference
    omega
  have potentialBound := Top.context_potential_change context block newBlock
    (credit := 3) (by omega) finalFits
  have logBound : Nat.log 2 capacity ≤ Nat.log 2 (capacity + 4) :=
    Nat.log_mono_right (by omega)
  have depthBound : Top.contextDepth context * Nat.log 2 (capacity + 4) ≤
      2 * Nat.log 2 (capacity + 4) := Nat.mul_le_mul_right _ shallow
  refine ⟨context.plug newBlock, exposedCount + (shapeCount + rawCount),
    matching.contains newBlock, exposeRun.append (Top.rotations_context context (shapeRun.append raw)), ?_⟩
  rw [blockSize] at shapeBound
  omega

end DynamicOptimality.MultiFinger

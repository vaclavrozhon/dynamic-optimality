import MultiSplay.RibRootOperations
import MultiSplay.SupportedPointer
import Splay.Accounting.OfflineRestrictedMacros

/-!
# Simulating a heavy macro in the persistent rib layer

The first layer's supported path is converted to shallow rotations with the
same endpoints. Each of those rotations updates the existing rib witness.
The rib potential telescopes through this entire macro; it is never restarted.
-/

namespace MultiSplay.Rib

open Splay.Tree (BST)
open Splay.Accounting.OfflineConnectedSupport
  (RibRepresentation HasSupportedPath RootPrefix SupportedPath ribs_of_height
   exists_restrictedPath_of_sameFrontier)
open TangoSquared.Paper20261030.Auxiliary (Rearranges rearranges_refl)

/-- The component's size is determined by its ordinal interval, regardless
of the source or normalizer shape. -/
theorem same_interval_size {lower upper : Nat} (a b : BST lower upper) : a.size = b.size := by
  have ha := a.size_add_lower_eq_upper
  have hb := b.size_add_lower_eq_upper
  omega

theorem simulate_shallow {capacity lower upper : Nat} {side : Bool}
    {before after actual : BST lower upper} {a : RootPrefix before} {b : RootPrefix after}
    (path : SupportedPath a b) (shallow : path.DepthBound 1)
    (representation : RibRepresentation capacity side before actual) (fits : before.size ≤ capacity) :
    ∃ final : BST lower upper, ∃ result : RibRepresentation capacity side after final, ∃ work : Nat,
      Rearranges (DynamicOptimality.BST.toRaw actual) (DynamicOptimality.BST.toRaw final) (18 * work) ∧
      work + result.potential ≤ representation.potential + 5388 * path.length := by
  induction path with
  | nil => exact ⟨actual, representation, 0, rearranges_refl _ 0, by simp [SupportedPath.length]⟩
  | @cons depth lower upper before middle after a b c rotation supported tail ih =>
      obtain ⟨rotated⟩ := exists_rotation rotation representation fits
      have nextFits : middle.size ≤ capacity := rotation.size_eq ▸ fits
      obtain ⟨final, result, work, run, bound⟩ := ih shallow.2 rotated.finalRep nextFits
      refine ⟨final, result, rotated.work + work, ?_, ?_⟩
      · simpa only [Nat.mul_add] using (supported_rearranges rotated.path).trans run
      · have first := rotated.amortized
        have depthBound := shallow.1
        simp only [SupportedPath.length]
        omega

/-- Only the support budget of the heavy macro is charged. The original
rotation count may be large, and is discarded by the proved shallow conversion. -/
theorem simulate_supported {capacity lower upper support rotations : Nat} {side : Bool}
    {before after actual : BST lower upper}
    (path : HasSupportedPath before after support rotations)
    (representation : RibRepresentation capacity side before actual) (fits : before.size ≤ capacity) :
    ∃ final : BST lower upper, ∃ result : RibRepresentation capacity side after final, ∃ work : Nat,
      Rearranges (DynamicOptimality.BST.toRaw actual) (DynamicOptimality.BST.toRaw final) (18 * work) ∧
      work + result.potential ≤ representation.potential + 21552 * support := by
  obtain ⟨a, b, execution, card, _⟩ := path
  by_cases positive : 0 < a.card
  · obtain ⟨restricted, lengthBound, shallow, _, _, _⟩ :=
      exists_restrictedPath_of_sameFrontier a b execution.toExecution.frontier_eq positive
        (ribs_of_height (slack := max before.height after.height) (le_max_left _ _))
        (ribs_of_height (le_max_right _ _))
    obtain ⟨final, result, work, run, bound⟩ := simulate_shallow restricted shallow representation fits
    exact ⟨final, result, work, run, by omega⟩
  · have same := execution.eq_of_card_zero (by omega)
    subst after
    exact ⟨actual, representation, 0, rearranges_refl _ 0, by omega⟩

end MultiSplay.Rib

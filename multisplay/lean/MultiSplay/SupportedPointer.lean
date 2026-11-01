import DynamicOptimality.ConnectedPointer
import Splay.Accounting.OfflineSupportedComposition

/-!
# Physical realization of a supported macro

`HasSupportedPath` records a connected set of touched keys and preserves its
untouched frontier subtrees. Its support bound pays for a genuine pointer
execution that starts and ends at the component root. No request is inserted.
-/

namespace MultiSplay

open TangoSquared.MTR TangoSquared.MTR.Tree
open TangoSquared.Paper20261030.Auxiliary (Rearranges rearranges_refl)
open Splay.Accounting.OfflineConnectedSupport (HasSupportedPath)

theorem restrictedSteps_rearranges {α : Type*} {a b : DynamicOptimality.RawTree α} {count : Nat}
    (steps : RestrictedSteps count a b) : Rearranges a b (3 * count) := by
  induction steps with
  | refl tree => exact rearranges_refl tree 0
  | cons step rest ih =>
      have h := (DynamicOptimality.restricted_pointer step).trans ih
      convert h using 1; omega

/-- This works for arbitrary indexed intervals, so a component need not use
the whole original universe or have lower endpoint zero. -/
theorem supported_rearranges {lower upper support rotations : Nat}
    {before after : DynamicOptimality.BST lower upper}
    (execution : HasSupportedPath before after support rotations) :
    Rearranges (DynamicOptimality.BST.toRaw before) (DynamicOptimality.BST.toRaw after)
      (18 * support) := by
  obtain ⟨a, b, path, card, _⟩ := execution
  have words := DynamicOptimality.supported_execution_marks path.toExecution
  let markedA := DynamicOptimality.markPrefix a
  let markedB := DynamicOptimality.markPrefix b
  have sameGaps : markedA.gapArray = markedB.gapArray := by
    funext i
    simp only [markedA, markedB, TangoSquared.MTR.Pointer.MarkedTree.gapArray, words.1]
  obtain ⟨count, countBound, steps⟩ :=
    graft_simulation_linear markedA.skeleton markedB.skeleton words.2 markedA.gapArray 0
  have source : graft markedA.skeleton markedA.gapArray 0 =
      DynamicOptimality.BST.toRaw before :=
    markedA.graft_gapArray.trans (DynamicOptimality.markPrefix_erase a)
  have target : graft markedB.skeleton markedA.gapArray 0 =
      DynamicOptimality.BST.toRaw after := by
    rw [sameGaps]
    exact markedB.graft_gapArray.trans (DynamicOptimality.markPrefix_erase b)
  have sameCard := path.toExecution.card_eq
  have sizeA := DynamicOptimality.markPrefix_size a
  have sizeB := DynamicOptimality.markPrefix_size b
  have budget : 3 * count ≤ 18 * support := by
    change count ≤ 3 * Tree.size (DynamicOptimality.markPrefix a).skeleton +
      3 * Tree.size (DynamicOptimality.markPrefix b).skeleton at countBound
    omega
  rw [source, target] at steps
  exact (restrictedSteps_rearranges steps).mono budget

end MultiSplay

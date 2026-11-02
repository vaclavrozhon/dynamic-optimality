import ChaCha.Paper20261030.GapBSTRepresentation
import ChaCha.Paper20261030.SourcePayloadCapacity
import DynamicOptimality.SearchRotationDepth

/-!
# Search depth after a completed preferred-path access

The requested key is the bottom of the exposed primary component. Its
gap-key encoding places that key at the root or the root's left child.
Thus the physical rotation trace also pays for the initial search, by
the usual change-of-depth bound for rotations.
-/

namespace ChaCha.Paper20261030.SplayAuxiliary.Global

open PrimaryPhysical ColoredStorage MTR.Tree

variable {α ρ : Type*} [LinearOrder α]

theorem component_bottom_searchDepth (left right : Wing α ρ) (bottom : α)
    (header : List ρ) (ordered : Ordered (GapBST.encode (component left right bottom header))) :
    ∃ depth ≤ 1, searchDepth bottom (GapBST.encode (component left right bottom header)) = some depth := by
  cases right with
  | none =>
      refine ⟨0,by decide,?_⟩
      cases left <;> simp [component,GapBST.encode,GapBST.lastKey]
  | some right =>
      have word : (wingLeaves left ++ [bottom] ++ right.shape.leaves).Pairwise (· < ·) := by
        simpa only [Ordered,GapBST.encode_word,component_leaves,wingLeaves] using ordered
      have lower : bottom < GapBST.lastKey right :=
        (List.pairwise_append.mp word).2.2 bottom (by simp) (GapBST.lastKey right) (by
          rw [← GapBST.gaps_word right]
          simp)
      refine ⟨1,le_rfl,?_⟩
      cases left <;>
        simp [component,GapBST.encode,GapBST.gaps,GapBST.lastKey,searchDepth,lower]

end ChaCha.Paper20261030.SplayAuxiliary.Global

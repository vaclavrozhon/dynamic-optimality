import TangoSquared.Paper20261030.PhysicalRectangleBound
import TangoSquared.Paper20261030.InitialComponents
import TangoSquared.Paper20261030.SourceInitialization

/-! The complete source-pointer bound from any initial full tree on the
canonical key word. Initialization is an actual linear-cost trace to the
explicit balanced component representation. Local acquisition of the
initial metadata and the ordinary-BST compiler are still separate. -/

namespace TangoSquared.Paper20261030.Dyadic

open ColoredStorage Rectangles Secondary SecondaryDecomposition LocalReferences SourcePointer PackedPrimary

def initialPhysicalState {h : Nat} (reference : DepthTree 0 h) : Source Int (List (Option (Datum Cached))) :=
  physicalState (canonical (h+1) 0)
    (initialComponents (completedDepth reference) (canonical (h+1) 0) (canonical_perfect (h+1) 0) (fun _ => true))

theorem initialPhysicalState_leaves {h : Nat} (reference : DepthTree 0 h) :
    (initialPhysicalState reference).shape.leaves = (canonical (h+1) 0).leaves :=
  initialComponents_leaves _ _ (canonical_perfect (h+1) 0) (canonical_nodup (h+1) 0) _

theorem initialized_physical_rectangle_bound {h : Nat} (reference : DepthTree 0 h)
    (before : Source Int (List (Option (Datum Cached))))
    (word : before.shape.leaves = (canonical (h+1) 0).leaves)
    (requests : List Int) (keys : ∀ key ∈ requests, ValidKey (h+1) key) :
    Rearranges before (initialPhysicalState reference) (14*2^(h+1)) ∧
    ∃ after : Source Int (List (Option (Datum Cached))),
      after.Bounded 5 ∧ after.shape.leaves = before.shape.leaves ∧
      Services (initialPhysicalState reference) requests after
        ((requests.length+13*rectangleBound (accessPoints requests)+6*2^(h+1)) * physicalRequestFactor reference) := by
  have init := initialize_source before (initialPhysicalState reference)
    (word.trans (initialPhysicalState_leaves reference).symm)
  have length : before.shape.leaves.length = 2^(h+1) := by
    rw [word]
    exact perfect_leaf_count (canonical_perfect (h+1) 0)
  rw [length] at init
  refine ⟨init,?_⟩
  obtain ⟨perfect,out,valid,execution⟩ := physical_run_rectangle_bound reference requests keys
    (initialComponents (completedDepth reference) (canonical (h+1) 0) (canonical_perfect (h+1) 0) (fun _ => true))
    (initialComponents_valid _ _ _ _)
  refine ⟨_,physicalState_bounded _ _,?_,execution⟩
  have leaves := execution.rearranges.leaves
  exact leaves.symm.trans ((initialPhysicalState_leaves reference).trans word.symm)

end TangoSquared.Paper20261030.Dyadic

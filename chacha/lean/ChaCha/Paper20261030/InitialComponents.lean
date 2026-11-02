import ChaCha.Paper20261030.MaintainedPhysicalState

/-! Constructing all endpoint-indexed secondary components. The construction
uses the existing balanced initialization, retains the original reference
records, and establishes the complete invariant for arbitrary initial
preferences. This module establishes representation; its statement does
not include the physical cost of initializing the whole structure. -/

namespace ChaCha.Paper20261030.SecondaryDecomposition

open ColoredStorage AuxiliaryComponent BoundaryObservations PathDecomposition
open PreferredProjection Secondary

variable {α : Type*} [DecidableEq α]

theorem componentSource_raw {height : Nat} (reference : DepthTree 0 height)
    (primary : PrefRouter α) (perfect : primary.Perfect height)
    (memory : MemoryKey → Bool) (key : α) :
    Raw (componentSource reference primary perfect memory key) := by
  unfold componentSource
  split
  · exact source_raw _ _
  · exact suffixSource_raw _ _ _ _

def initialComponents {height : Nat} (reference : DepthTree 0 height)
    (primary : PrefRouter α) (perfect : primary.Perfect height)
    (memory : MemoryKey → Bool) : Components α :=
  fun key => initializeMarked followsRight (componentSource reference primary perfect memory key)

theorem initialComponents_valid {height : Nat} (reference : DepthTree 0 height)
    (primary : PrefRouter α) (perfect : primary.Perfect height) (memory : MemoryKey → Bool) :
    Components.Valid reference primary perfect memory (initialComponents reference primary perfect memory) :=
  fun key _ => initialize_represents followsRight _ (componentSource_raw reference primary perfect memory key)

theorem initialComponents_leaves {height : Nat} (reference : DepthTree 0 height)
    (primary : PrefRouter α) (perfect : primary.Perfect height) (distinct : primary.leaves.Nodup)
    (memory : MemoryKey → Bool) :
    (physicalState primary (initialComponents reference primary perfect memory)).shape.leaves = primary.leaves :=
  (initialComponents_valid reference primary perfect memory).physical_leaves reference perfect distinct memory _

end ChaCha.Paper20261030.SecondaryDecomposition

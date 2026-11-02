import MultiSplay.ComparatorStableSuffix
import MultiSplay.ComparatorSuffixAccounting
import MultiSplay.ComparatorGapProgram

/-! # Access with persistent interval identities

An induced suffix has an auxiliary name for each clipped interval. The
stable representation uses the corresponding interval of the fixed original
reference. The name conversion leaves the actual gap BST identical, so the
charged program consists only of the proved access and structural repair.
The persistent memory changes only on genuine original intervals.
-/

namespace MultiSplay.ComparatorStableSuffix

open ChaCha
open Paper20261030
open ColoredStorage Auxiliary AuxiliaryComponent BoundaryObservations PathDecomposition
open SecondaryDecomposition
open ComparatorSuffix

/-- The actual comparator BST is maintained across the logical renaming on
both sides of the access. No initialization or owner reset occurs here. -/
theorem access_program {a b : Nat} (reference : DepthTree a b)
    (start : Nat) (lo : a ≤ start) (hi : start ≤ b) (request : Nat)
    (memory : DepthSplit → Bool)
    (component : AuxiliaryComponent Nat Nat (Tagged Payload))
    (represented : Represents followsRight
      (suffixSource reference (bits start memory) start ⟨lo,hi⟩) component) :
    ∃ out : AuxiliaryComponent Nat Nat (Tagged Payload),
      Represents followsRight
        (suffixSource reference (bits start (writeGenuine start request memory)) start ⟨lo,hi⟩) out ∧
      ∃ work ≤ 12 * ((genuineCost reference start request memory + 2) * repairBound reference + 1),
        CommonForest.Program [GapBST.gaps (closed component)] [] [GapBST.gaps (closed out)] work := by
  have clipped := ComparatorRecords.represents (clip start) represented
  rw [clip_source reference start lo hi memory] at clipped
  obtain ⟨changed,changedRep,execution⟩ := access_genuine_charged reference start lo hi request memory
    (ComparatorRecords.component (clip start) component) clipped
  have restored := ComparatorRecords.represents (originalName reference) changedRep
  rw [restore_source reference start lo hi (writeGenuine start request memory)] at restored
  obtain ⟨work,bound,program⟩ := ComparatorGap.rearranges_program execution
  refine ⟨ComparatorRecords.component (originalName reference) changed,restored,work,bound,?_⟩
  simpa only [ComparatorRecords.physical_eq] using program

end MultiSplay.ComparatorStableSuffix

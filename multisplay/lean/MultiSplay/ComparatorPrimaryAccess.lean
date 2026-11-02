import MultiSplay.ComparatorPrimaryProjection
import MultiSplay.ComparatorPreparedAccess
import ChaCha.Paper20261030.DecompositionLeaves

/-! # Stable suffix access on the actual preferred-path keys

The input ties the maintained secondary component to the concrete primary
projection by equality of its erased source. The transition constructs the
new maintained component and the new projection together. The actual
program has the exact old and new original-key trees as endpoints.
-/

namespace MultiSplay.ComparatorPrimary

open ChaCha
open Paper20261030
open ColoredStorage Auxiliary AuxiliaryComponent BoundaryObservations PathDecomposition
open SecondaryDecomposition
open ComparatorSuffix ComparatorStableSuffix
open Secondary (intervalUpdate)

/-- A stable suffix has exactly its ordinary depth alphabet, even though
its intervals retain their original names. -/
theorem stable_leaf_word {a b : Nat} (reference : DepthTree a b) (start : Nat)
    (valid : a ≤ start ∧ start ≤ b) (memory : DepthSplit → Bool)
    (component : AuxiliaryComponent Nat Nat (Tagged Payload))
    (represented : Represents followsRight
      (suffixSource reference (bits start memory) start valid) component) :
    (ComparatorRecords.erase (closed component)).shape.leaves = List.range' start (b+1-start) := by
  have clipped := ComparatorRecords.represents (clip start) represented
  rw [clip_source reference start valid.1 valid.2 memory] at clipped
  have word := represented_leaf_word (suffix reference start valid.1 valid.2)
    (preference reference start memory) _ clipped
  simpa only [ComparatorRecords.erase,ComparatorRecords.closed_map,Source.mapRecords_shape] using word

/-- Every concrete stable suffix whose length matches the current primary
path supplies an actual input; no future transition is assumed. -/
def input {lower upper a b : Nat} (state : EndpointEncoding.State)
    (primary : DynamicOptimality.BST lower upper) (reference : DepthTree a b)
    (start : Nat) (valid : a ≤ start ∧ start ≤ b) (memory : DepthSplit → Bool)
    (component : AuxiliaryComponent Nat Nat (Tagged Payload))
    (represented : Represents followsRight
      (suffixSource reference (bits start memory) start valid) component)
    (length : b = start + (PrimaryWings.exits (routing state primary)).length) :
    PackedPrimary.Input (routing state primary) Unit where
  start := start
  source := ComparatorRecords.erase (closed component)
  leaves := Or.inl (by
    rw [stable_leaf_word reference start valid memory component represented]
    congr 1
    omega)

theorem prepare_original_program {lower upper a b : Nat} (state : EndpointEncoding.State)
    (primary : DynamicOptimality.BST lower upper) (reference : DepthTree a b)
    (start : Nat) (valid : a ≤ start ∧ start ≤ b) (request : Nat)
    (inSuffix : start ≤ request) (memory : DepthSplit → Bool)
    (component : AuxiliaryComponent Nat Nat (Tagged Payload))
    (represented : Represents followsRight
      (suffixSource reference (bits start memory) start valid) component)
    (before : PackedPrimary.Input (routing state primary) Unit)
    (sourceEq : before.source = ComparatorRecords.erase (closed component)) :
    ∃ (out : AuxiliaryComponent Nat Nat (Tagged Payload))
      (after : PackedPrimary.Input (routing state primary) Unit),
      Represents followsRight
        (suffixSource reference (intervalUpdate request (bits start memory)) start valid) out ∧
      after.source = ComparatorRecords.erase (closed out) ∧ after.start = before.start ∧
      ∃ work ≤ 816 * ((genuineCost reference start request memory + 1) * SecondaryDecomposition.repairBound reference) + 156,
        CommonForest.Program [tree state primary before] [] [tree state primary after] work := by
  obtain ⟨out,outRep,run⟩ := prepare_erased_charged reference start valid.1 valid.2 request
    inSuffix memory component represented
  rw [← sourceEq] at run
  let after := before.withSource (ComparatorRecords.erase (closed out)) run.leaves
  obtain ⟨work,bound,program⟩ := source_program state primary before after rfl run
  exact ⟨out,after,outRep,rfl,rfl,work,bound,program⟩

end MultiSplay.ComparatorPrimary

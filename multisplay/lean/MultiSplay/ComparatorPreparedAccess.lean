import MultiSplay.ComparatorStableAccess

/-! # The prepared endpoint before structural restoration

For a request inside the suffix, updating clipped intervals and restoring
their original names commutes with the ordinary depth preference update.
This exposes the prepared intermediate state needed by the actual tail
cut. Only genuine writes are charged to persistent memory; the bound
allows the single structural departure separately.
-/

namespace MultiSplay.ComparatorStableSuffix

open ChaCha
open Paper20261030
open ColoredStorage Auxiliary AuxiliaryComponent BoundaryObservations PathDecomposition
open SecondaryDecomposition
open ComparatorSuffix
open Secondary (intervalUpdate)

theorem restore_updated_genuine {x y a b : Nat}
    (original : DepthTree x y) (reference : DepthTree a b)
    (included : reference.nodes ⊆ original.nodes) (start request : Nat) (lower : start ≤ a)
    (memory : DepthSplit → Bool) :
    (source reference (intervalUpdate request (preference original start memory))).mapRecords
      (ComparatorRecords.record (originalName original)) =
        source reference (intervalUpdate request (bits start memory)) := by
  apply map_source
  · intro split member
    have genuine : start ≤ split.lo := lower.trans (reference.node_bounds member).1
    refine ⟨originalName_node original (included member),?_⟩
    simp only [intervalUpdate]
    split
    · rfl
    · rw [preference_genuine original start memory (included member) genuine]
      simp only [bits,if_neg (by omega : ¬split.lo < start)]
  · intro key _ _
    exact originalName_leaf original key

theorem restore_updated_source_of_subset {x y a b : Nat}
    (original : DepthTree x y) (reference : DepthTree a b)
    (included : reference.nodes ⊆ original.nodes) (start request : Nat)
    (lower : a ≤ start) (upper : start ≤ b) (inSuffix : start ≤ request)
    (memory : DepthSplit → Bool) :
    (source (suffix reference start lower upper)
      (intervalUpdate request (preference original start memory))).mapRecords
      (ComparatorRecords.record (originalName original)) =
        suffixSource reference (intervalUpdate request (bits start memory)) start ⟨lower,upper⟩ := by
  induction reference with
  | leaf a =>
      have equal : start = a := by omega
      subst start
      simp only [suffix,source,suffixSource,terminalLeaf,Source.mapRecords,
        ComparatorRecords.record,ComparatorRecords.value,originalName_leaf]
  | @node a b cut ha hb left right ihl ihr =>
      have leftIncluded : left.nodes ⊆ original.nodes := fun _ member => included (by simp [DepthTree.nodes,member])
      have rightIncluded : right.nodes ⊆ original.nodes := fun _ member => included (by simp [DepthTree.nodes,member])
      by_cases retained : start ≤ cut
      · have member : (⟨a,cut,b⟩ : DepthSplit) ∈ original.nodes := included (by simp [DepthTree.nodes])
        have rootName : originalName original ⟨start,cut,b⟩ = ⟨a,cut,b⟩ := by
          simp only [originalName,if_pos hb,original_of_cut original member,Option.getD_some]
        have rootBit : intervalUpdate request (preference original start memory) ⟨start,cut,b⟩ =
            intervalUpdate request (bits start memory) ⟨a,cut,b⟩ := by
          have lo : a ≤ request := lower.trans inSuffix
          simp only [intervalUpdate,inSuffix,lo,true_and,preference,original_of_cut original member,bits]
        have leftEq := ihl leftIncluded lower retained
        have rightEq := restore_updated_genuine original right rightIncluded start request (by omega) memory
        simp only [suffix,dif_pos retained,source,Source.mapRecords,ComparatorRecords.record,
          ComparatorRecords.value,suffixSource,rootName,rootBit,leftEq,rightEq]
      · simpa only [suffix,suffixSource,dif_neg retained] using ihr rightIncluded (by omega) upper

/-- A fixed actual preparation program with the exact stable source as its
endpoint. Unlike the completed access, this endpoint keeps the structural
bits needed to expose the requested existing separator. -/
theorem prepare_program {a b : Nat} (reference : DepthTree a b)
    (start : Nat) (lo : a ≤ start) (hi : start ≤ b) (request : Nat)
    (inSuffix : start ≤ request) (memory : DepthSplit → Bool)
    (component : AuxiliaryComponent Nat Nat (Tagged Payload))
    (represented : Represents followsRight
      (suffixSource reference (bits start memory) start ⟨lo,hi⟩) component) :
    ∃ out : AuxiliaryComponent Nat Nat (Tagged Payload),
      Represents followsRight
        (suffixSource reference (intervalUpdate request (bits start memory)) start ⟨lo,hi⟩) out ∧
      ∃ work ≤ 12 * ((genuineCost reference start request memory + 1) * SecondaryDecomposition.repairBound reference + 1),
        CommonForest.Program [GapBST.gaps (closed component)] [] [GapBST.gaps (closed out)] work := by
  have clipped := ComparatorRecords.represents (clip start) represented
  rw [clip_source reference start lo hi memory] at clipped
  obtain ⟨changed,changedRep,execution⟩ := access_rearrangement
    (suffix reference start lo hi) (preference reference start memory) request
    (ComparatorRecords.component (clip start) component) clipped
  have restored := ComparatorRecords.represents (originalName reference) changedRep
  rw [restore_updated_source_of_subset reference reference (fun _ h => h) start request lo hi inSuffix memory] at restored
  obtain ⟨work,bound,program⟩ := ComparatorGap.rearranges_program execution
  have flips := accessFlips_le_genuine reference start lo hi request memory
  have height := suffix_height reference start lo hi
  have logarithm := Nat.clog_monotone 2 (Nat.add_le_add_right height 1)
  have repair : SecondaryDecomposition.repairBound (suffix reference start lo hi) ≤
      SecondaryDecomposition.repairBound reference := by
    unfold SecondaryDecomposition.repairBound
    omega
  have total := Nat.mul_le_mul flips repair
  refine ⟨ComparatorRecords.component (originalName reference) changed,restored,work,by omega,?_⟩
  simpa only [ComparatorRecords.physical_eq] using program

theorem prepared_terminal {a b : Nat} (reference : DepthTree a b) (start request : Nat)
    (memory : DepthSplit → Bool) (valid : a ≤ request ∧ request ≤ b) :
    (Secondary.decodeDepth reference (intervalUpdate request (bits start memory))).terminal = request := by
  rw [Secondary.decodeDepth_access]
  exact PreferredProjection.PrefRouter.terminal_access request _
    ((Secondary.decodeDepth_mem reference _ request).mpr valid)


/-- The prepared transaction as an actual source trace with ghost record
fields erased. This is the form consumed by original-key primary unfolding;
renaming an interval is literally equality of these source endpoints. -/
theorem prepare_erased_charged {a b : Nat} (reference : DepthTree a b)
    (start : Nat) (lo : a ≤ start) (hi : start ≤ b) (request : Nat)
    (inSuffix : start ≤ request) (memory : DepthSplit → Bool)
    (component : AuxiliaryComponent Nat Nat (Tagged Payload))
    (represented : Represents followsRight
      (suffixSource reference (bits start memory) start ⟨lo,hi⟩) component) :
    ∃ out : AuxiliaryComponent Nat Nat (Tagged Payload),
      Represents followsRight
        (suffixSource reference (intervalUpdate request (bits start memory)) start ⟨lo,hi⟩) out ∧
      SourcePointer.Rearranges (ComparatorRecords.erase (closed component))
        (ComparatorRecords.erase (closed out))
        ((genuineCost reference start request memory + 1) * SecondaryDecomposition.repairBound reference) := by
  have clipped := ComparatorRecords.represents (clip start) represented
  rw [clip_source reference start lo hi memory] at clipped
  obtain ⟨changed,changedRep,execution⟩ := access_rearrangement
    (suffix reference start lo hi) (preference reference start memory) request
    (ComparatorRecords.component (clip start) component) clipped
  have restored := ComparatorRecords.represents (originalName reference) changedRep
  rw [restore_updated_source_of_subset reference reference (fun _ h => h) start request lo hi inSuffix memory] at restored
  have run := execution.mapRecords (fun _ => ())
  change SourcePointer.Rearranges (ComparatorRecords.erase (closed (ComparatorRecords.component (clip start) component)))
    (ComparatorRecords.erase (closed changed)) _ at run
  rw [ComparatorRecords.erase_component] at run
  have flips := accessFlips_le_genuine reference start lo hi request memory
  have height := suffix_height reference start lo hi
  have logarithm := Nat.clog_monotone 2 (Nat.add_le_add_right height 1)
  have repair : SecondaryDecomposition.repairBound (suffix reference start lo hi) ≤
      SecondaryDecomposition.repairBound reference := by
    unfold SecondaryDecomposition.repairBound
    omega
  refine ⟨ComparatorRecords.component (originalName reference) changed,restored,?_⟩
  rw [ComparatorRecords.erase_component]
  exact run.mono (Nat.mul_le_mul flips repair)

end MultiSplay.ComparatorStableSuffix

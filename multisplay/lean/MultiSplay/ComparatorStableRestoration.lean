import MultiSplay.ComparatorPreparedAccess
import TangoSquared.Paper20261030.HeadMemorySplice

/-! # Structural restoration after the source splice

The actual splice keeps the prepared old prefix and the incoming genuine
suffix. Updating, splicing, and reading stable interval names commute.
Only the structural boundary is restored afterwards; its actual charged
repair changes no additional persistent owner bit.
-/

namespace MultiSplay.ComparatorStableSuffix

open TangoSquared
open Paper20261030
open ColoredStorage Auxiliary AuxiliaryComponent BoundaryObservations PathDecomposition
open SecondaryDecomposition
open ComparatorSuffix
open Secondary (intervalUpdate spliceBits)

theorem clip_updated_genuine {x y a b : Nat}
    (original : DepthTree x y) (reference : DepthTree a b)
    (included : reference.nodes ⊆ original.nodes) (start request : Nat) (lower : start ≤ a)
    (memory : DepthSplit → Bool) :
    (source reference (intervalUpdate request (bits start memory))).mapRecords
      (ComparatorRecords.record (clip start)) =
        source reference (intervalUpdate request (preference original start memory)) := by
  apply map_source
  · intro split member
    have genuine : start ≤ split.lo := lower.trans (reference.node_bounds member).1
    refine ⟨clip_genuine start split genuine,?_⟩
    simp only [intervalUpdate]
    split
    · rfl
    · rw [preference_genuine original start memory (included member) genuine]
      simp only [bits,if_neg (by omega : ¬split.lo < start)]
  · intro key lo _
    exact clip_leaf start key (lower.trans lo)

theorem clip_updated_source_of_subset {x y a b : Nat}
    (original : DepthTree x y) (reference : DepthTree a b)
    (included : reference.nodes ⊆ original.nodes) (start request : Nat)
    (lower : a ≤ start) (upper : start ≤ b) (inSuffix : start ≤ request)
    (memory : DepthSplit → Bool) :
    (suffixSource reference (intervalUpdate request (bits start memory)) start ⟨lower,upper⟩).mapRecords
      (ComparatorRecords.record (clip start)) =
        source (suffix reference start lower upper) (intervalUpdate request (preference original start memory)) := by
  induction reference with
  | leaf a =>
      have equal : start = a := by omega
      subst start
      simp only [suffix,source,suffixSource,terminalLeaf,Source.mapRecords,
        ComparatorRecords.record,ComparatorRecords.value,clip_leaf a a le_rfl]
  | @node a b cut ha hb left right ihl ihr =>
      have leftIncluded : left.nodes ⊆ original.nodes := fun _ member => included (by simp [DepthTree.nodes,member])
      have rightIncluded : right.nodes ⊆ original.nodes := fun _ member => included (by simp [DepthTree.nodes,member])
      by_cases retained : start ≤ cut
      · have member : (⟨a,cut,b⟩ : DepthSplit) ∈ original.nodes := included (by simp [DepthTree.nodes])
        have rootName : clip start ⟨a,cut,b⟩ = ⟨start,cut,b⟩ := by simp only [clip,max_eq_left lower]
        have rootBit : intervalUpdate request (preference original start memory) ⟨start,cut,b⟩ =
            intervalUpdate request (bits start memory) ⟨a,cut,b⟩ := by
          have lo : a ≤ request := lower.trans inSuffix
          simp only [intervalUpdate,inSuffix,lo,true_and,preference,original_of_cut original member,bits]
        have leftEq := ihl leftIncluded lower retained
        have rightEq := clip_updated_genuine original right rightIncluded start request (by omega) memory
        simp only [suffix,dif_pos retained,source,Source.mapRecords,ComparatorRecords.record,
          ComparatorRecords.value,suffixSource,rootName,rootBit,leftEq,rightEq]
      · simpa only [suffix,suffixSource,dif_neg retained] using ihr rightIncluded (by omega) upper

/-- This is the sole post-splice structural repair, with the exact same
actual erased source as input. Its output memory is proved, not assumed. -/
theorem restore_erased_charged {a b : Nat} (reference : DepthTree a b)
    (start : Nat) (valid : a ≤ start ∧ start ≤ b) (request : Nat)
    (inSuffix : start ≤ request) (memory : DepthSplit → Bool)
    (component : AuxiliaryComponent Nat Nat (Tagged Payload))
    (represented : Represents followsRight
      (suffixSource reference (intervalUpdate request (bits start memory)) start valid) component) :
    ∃ out : AuxiliaryComponent Nat Nat (Tagged Payload),
      Represents followsRight
        (suffixSource reference (bits start (writeGenuine start request memory)) start valid) out ∧
      SourcePointer.Rearranges (ComparatorRecords.erase (closed component))
        (ComparatorRecords.erase (closed out)) (SecondaryDecomposition.repairBound reference) := by
  have clipped := ComparatorRecords.represents (clip start) represented
  rw [clip_updated_source_of_subset reference reference (fun _ h => h) start request
    valid.1 valid.2 inSuffix memory] at clipped
  obtain ⟨changed,changedRep,execution⟩ := restore_charged reference start valid.1 valid.2 request memory
    (ComparatorRecords.component (clip start) component) clipped
  have restored := ComparatorRecords.represents (originalName reference) changedRep
  rw [restore_source reference start valid.1 valid.2 (writeGenuine start request memory)] at restored
  have run := execution.mapRecords (fun _ => ())
  change SourcePointer.Rearranges (ComparatorRecords.erase (closed (ComparatorRecords.component (clip start) component)))
    (ComparatorRecords.erase (closed changed)) _ at run
  rw [ComparatorRecords.erase_component] at run
  refine ⟨ComparatorRecords.component (originalName reference) changed,restored,?_⟩
  rwa [ComparatorRecords.erase_component]

theorem bits_splice (start d : Nat) (old incoming : DepthSplit → Bool) :
    bits start (spliceBits d old incoming) = spliceBits d (bits start old) (bits start incoming) := by
  funext split
  simp only [bits,spliceBits]
  split <;> split <;> rfl

theorem update_splice (d : Nat) (old incoming : DepthSplit → Bool) :
    spliceBits d (intervalUpdate d old) (intervalUpdate d incoming) =
      intervalUpdate d (spliceBits d old incoming) := by
  funext split
  by_cases lower : split.lo ≤ d
  · simp only [spliceBits,if_pos lower,intervalUpdate]
  · simp only [spliceBits,if_neg lower,intervalUpdate,if_neg (by omega : ¬(split.lo ≤ d ∧ d ≤ split.hi))]

theorem prepared_splice (start d : Nat) (old incoming : DepthSplit → Bool) :
    spliceBits d (intervalUpdate d (bits start old)) (intervalUpdate d (bits start incoming)) =
      intervalUpdate d (bits start (spliceBits d old incoming)) := by
  rw [update_splice,bits_splice]

theorem write_splice (start d : Nat) (old incoming : DepthSplit → Bool) :
    writeGenuine start d (spliceBits d old incoming) = spliceBits d (writeGenuine start d old) incoming := by
  funext split
  by_cases lower : split.lo ≤ d
  · simp only [writeGenuine,spliceBits,if_pos lower,intervalUpdate]
  · simp only [writeGenuine,spliceBits,if_neg lower,intervalUpdate,
      if_neg (by omega : ¬(split.lo ≤ d ∧ d ≤ split.hi))]
    split <;> rfl

end MultiSplay.ComparatorStableSuffix

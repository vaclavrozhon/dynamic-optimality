import MultiSplay.ComparatorPreparedAccess

/-! # The detached tail reads the unchanged persistent memory

The prepared access to depth `d` changes only intervals meeting `d`.
Restricting to the tail starting at `d+1` discards every right-pointing
boundary interval; the retained crossing intervals point left. The result
is exactly the ordinary stable suffix convention, without memory resets.
-/

namespace MultiSplay.ComparatorStableSuffix

open ChaCha
open Paper20261030
open Std Std.DTreeMap.Internal Std.DTreeMap.Internal.Impl
open ColoredStorage Auxiliary AuxiliaryComponent BoundaryObservations PathDecomposition
open SecondaryDecomposition
open ComparatorSuffix
open Secondary (intervalUpdate)

theorem suffixSource_congr {a b : Nat} (reference : DepthTree a b)
    (before after : DepthSplit → Bool) (start : Nat) (valid : a ≤ start ∧ start ≤ b)
    (same : ∀ split ∈ reference.nodes, start ≤ split.cut → before split = after split) :
    suffixSource reference before start valid = suffixSource reference after start valid := by
  induction reference with
  | leaf => rfl
  | @node a b cut ha hb left right ihl ihr =>
      by_cases kept : start ≤ cut
      · have root := same ⟨a,cut,b⟩ (by simp [DepthTree.nodes]) kept
        have l := ihl ⟨valid.1,kept⟩ (fun split member bound => same split (by simp [DepthTree.nodes,member]) bound)
        have r : source right before = source right after := by
          apply source_congr
          intro split member
          have bounds := right.node_bounds member
          exact same split (by simp [DepthTree.nodes,member]) (by omega)
        simp only [suffixSource,dif_pos kept,root,l,r]
      · simpa only [suffixSource,dif_neg kept] using
          ihr ⟨by omega,valid.2⟩ (fun split member bound => same split (by simp [DepthTree.nodes,member]) bound)

theorem prepared_tail_source {a b : Nat} (reference : DepthTree a b)
    (start d : Nat) (earlier : start ≤ d) (valid : a ≤ d+1 ∧ d+1 ≤ b)
    (memory : DepthSplit → Bool) :
    suffixSource reference (intervalUpdate d (bits start memory)) (d+1) valid =
      suffixSource reference (bits (d+1) memory) (d+1) valid := by
  apply suffixSource_congr
  intro split member retained
  have bounds := reference.node_bounds member
  by_cases crosses : split.lo ≤ d
  · have inside : split.lo ≤ d ∧ d ≤ split.hi := by omega
    simp only [intervalUpdate,if_pos inside,bits,if_pos (by omega : split.lo < d+1),
      decide_eq_false (by omega : ¬split.cut < d)]
  · have outside : ¬(split.lo ≤ d ∧ d ≤ split.hi) := by omega
    simp only [intervalUpdate,if_neg outside,bits,
      if_neg (by omega : ¬split.lo < start),if_neg (by omega : ¬split.lo < d+1)]

theorem writeGenuine_deeper (start d : Nat) (memory : DepthSplit → Bool)
    (split : DepthSplit) (deeper : d < split.lo) :
    writeGenuine start d memory split = memory split := by
  simp only [writeGenuine,intervalUpdate,if_neg (by omega : ¬(split.lo ≤ d ∧ d ≤ split.hi))]
  split <;> rfl

theorem tail_memory_unchanged (start d : Nat) (memory : DepthSplit → Bool) :
    bits (d+1) (writeGenuine start d memory) = bits (d+1) memory := by
  funext split
  simp only [bits]
  split
  · rfl
  · exact writeGenuine_deeper start d memory split (by omega)

/-- Order follows from the represented induced reference. Renaming ghost
intervals does not change any separator key in the core word. -/
theorem represented_stable_ordered {a b : Nat} (reference : DepthTree a b)
    (start : Nat) (valid : a ≤ start ∧ start ≤ b) (memory : DepthSplit → Bool)
    (component : AuxiliaryComponent Nat Nat (Tagged Payload))
    (represented : Represents followsRight
      (suffixSource reference (bits start memory) start valid) component) : component.core.Ordered := by
  have clipped := ComparatorRecords.represents (clip start) represented
  rw [clip_source reference start valid.1 valid.2 memory] at clipped
  have ordered := represented_ordered (suffix reference start valid.1 valid.2)
    (preference reference start memory) _ clipped
  change ((component.core.map (ComparatorRecords.value (clip start))).toListModel).Pairwise _ at ordered
  rw [ComparatorRecords.core_word,List.pairwise_map] at ordered
  exact ordered

end MultiSplay.ComparatorStableSuffix

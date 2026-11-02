import MultiSplay.ComparatorStableRestoration
import MultiSplay.ComparatorStableSeams
import ChaCha.Paper20261030.PreparedPrefixJoin

/-! # Restricting a prepared path at an arbitrary component start

The secondary reference uses the fixed global depth alphabet. A primary
component may begin at any depth. These identities transport the existing
balanced cut and join proofs through the induced reference, while retaining
the original names of genuine intervals.
-/

namespace MultiSplay.ComparatorStableSuffix

open ChaCha
open Paper20261030
open ColoredStorage Auxiliary AuxiliaryComponent BoundaryObservations PathDecomposition
open SecondaryDecomposition ComparatorSuffix
open Secondary (intervalUpdate spliceBits)
open Std Std.DTreeMap.Internal Std.DTreeMap.Internal.Impl

theorem map_suffixSource {a b : Nat} (reference : DepthTree a b)
    (rename : DepthSplit → DepthSplit) (before after : DepthSplit → Bool)
    (nodes : ∀ split ∈ reference.nodes, rename split = split ∧ before split = after split)
    (leaves : ∀ key, a ≤ key → key ≤ b → rename ⟨key,key,key⟩ = ⟨key,key,key⟩)
    (d : Nat) (valid : a ≤ d ∧ d ≤ b) :
    (suffixSource reference before d valid).mapRecords (ComparatorRecords.record rename) =
      suffixSource reference after d valid := by
  induction reference with
  | leaf a =>
      simp only [suffixSource,terminalLeaf,Source.mapRecords,ComparatorRecords.record,
        ComparatorRecords.value,leaves a le_rfl le_rfl]
  | @node a b cut ha hb left right ihl ihr =>
      have leftNodes : ∀ split ∈ left.nodes, rename split = split ∧ before split = after split :=
        fun split member => nodes split (by simp [DepthTree.nodes,member])
      have rightNodes : ∀ split ∈ right.nodes, rename split = split ∧ before split = after split :=
        fun split member => nodes split (by simp [DepthTree.nodes,member])
      by_cases retained : d ≤ cut
      · obtain ⟨rootName,rootBit⟩ := nodes ⟨a,cut,b⟩ (by simp [DepthTree.nodes])
        have leftEq := ihl leftNodes (fun key lo hi => leaves key lo (by omega)) ⟨valid.1,retained⟩
        have rightEq := map_source right rename before after rightNodes
          (fun key lo hi => leaves key (by omega) hi)
        simp only [suffixSource,dif_pos retained,Source.mapRecords,ComparatorRecords.record,
          ComparatorRecords.value,rootName,rootBit,leftEq,rightEq]
      · simpa only [suffixSource,dif_neg retained] using
          ihr rightNodes (fun key lo hi => leaves key (by omega) hi) ⟨by omega,valid.2⟩

theorem restore_updated_suffix_genuine {x y a b : Nat}
    (original : DepthTree x y) (reference : DepthTree a b)
    (included : reference.nodes ⊆ original.nodes) (start request : Nat) (lower : start ≤ a)
    (memory : DepthSplit → Bool) (d : Nat) (valid : a ≤ d ∧ d ≤ b) :
    (suffixSource reference (intervalUpdate request (preference original start memory)) d valid).mapRecords
      (ComparatorRecords.record (originalName original)) =
        suffixSource reference (intervalUpdate request (bits start memory)) d valid := by
  apply map_suffixSource
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

theorem restore_updated_suffix_of_subset {x y a b : Nat}
    (original : DepthTree x y) (reference : DepthTree a b)
    (included : reference.nodes ⊆ original.nodes) (start request d : Nat)
    (lower : a ≤ start) (upper : start ≤ b) (inSuffix : start ≤ request)
    (valid : start ≤ d ∧ d ≤ b) (memory : DepthSplit → Bool) :
    (suffixSource (suffix reference start lower upper)
      (intervalUpdate request (preference original start memory)) d valid).mapRecords
      (ComparatorRecords.record (originalName original)) =
        suffixSource reference (intervalUpdate request (bits start memory)) d
          ⟨lower.trans valid.1,valid.2⟩ := by
  induction reference with
  | leaf a =>
      have same : start = a := by omega
      subst start
      have sameD : d = a := by omega
      subst d
      simp only [suffix,suffixSource,terminalLeaf,Source.mapRecords,ComparatorRecords.record,
        ComparatorRecords.value,originalName_leaf]
  | @node a b cut ha hb left right ihl ihr =>
      have leftIncluded : left.nodes ⊆ original.nodes := fun _ member => included (by simp [DepthTree.nodes,member])
      have rightIncluded : right.nodes ⊆ original.nodes := fun _ member => included (by simp [DepthTree.nodes,member])
      by_cases retained : start ≤ cut
      · by_cases keep : d ≤ cut
        · have member : (⟨a,cut,b⟩ : DepthSplit) ∈ original.nodes := included (by simp [DepthTree.nodes])
          have rootName : originalName original ⟨start,cut,b⟩ = ⟨a,cut,b⟩ := by
            simp only [originalName,if_pos hb,original_of_cut original member,Option.getD_some]
          have rootBit : intervalUpdate request (preference original start memory) ⟨start,cut,b⟩ =
              intervalUpdate request (bits start memory) ⟨a,cut,b⟩ := by
            have lo : a ≤ request := lower.trans inSuffix
            simp only [intervalUpdate,inSuffix,lo,true_and,preference,original_of_cut original member,bits]
          have leftEq := ihl leftIncluded lower retained ⟨valid.1,keep⟩
          have rightEq := restore_updated_genuine original right rightIncluded start request (by omega) memory
          simp only [suffix,dif_pos retained,suffixSource,dif_pos keep,Source.mapRecords,
            ComparatorRecords.record,ComparatorRecords.value,rootName,rootBit,leftEq,rightEq]
        · simpa only [suffix,dif_pos retained,suffixSource,dif_neg keep] using
            restore_updated_suffix_genuine original right rightIncluded start request (by omega)
              memory d ⟨by omega,valid.2⟩
      · have keep : ¬d ≤ cut := by omega
        simpa only [suffix,dif_neg retained,suffixSource,dif_neg keep] using
          ihr rightIncluded (by omega) upper valid

theorem clip_updated_suffix_genuine {x y a b : Nat}
    (original : DepthTree x y) (reference : DepthTree a b)
    (included : reference.nodes ⊆ original.nodes) (start request : Nat) (lower : start ≤ a)
    (memory : DepthSplit → Bool) (d : Nat) (valid : a ≤ d ∧ d ≤ b) :
    (suffixSource reference (intervalUpdate request (bits start memory)) d valid).mapRecords
      (ComparatorRecords.record (clip start)) =
        suffixSource reference (intervalUpdate request (preference original start memory)) d valid := by
  apply map_suffixSource
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

theorem clip_updated_suffix_of_subset {x y a b : Nat}
    (original : DepthTree x y) (reference : DepthTree a b)
    (included : reference.nodes ⊆ original.nodes) (start request d : Nat)
    (lower : a ≤ start) (upper : start ≤ b) (inSuffix : start ≤ request)
    (valid : start ≤ d ∧ d ≤ b) (memory : DepthSplit → Bool) :
    (suffixSource reference (intervalUpdate request (bits start memory)) d
      ⟨lower.trans valid.1,valid.2⟩).mapRecords (ComparatorRecords.record (clip start)) =
      suffixSource (suffix reference start lower upper)
        (intervalUpdate request (preference original start memory)) d valid := by
  induction reference with
  | leaf a =>
      have same : start = a := by omega
      subst start
      have sameD : d = a := by omega
      subst d
      simp only [suffix,suffixSource,terminalLeaf,Source.mapRecords,ComparatorRecords.record,
        ComparatorRecords.value,clip_leaf a a le_rfl]
  | @node a b cut ha hb left right ihl ihr =>
      have leftIncluded : left.nodes ⊆ original.nodes := fun _ member => included (by simp [DepthTree.nodes,member])
      have rightIncluded : right.nodes ⊆ original.nodes := fun _ member => included (by simp [DepthTree.nodes,member])
      by_cases retained : start ≤ cut
      · by_cases keep : d ≤ cut
        · have member : (⟨a,cut,b⟩ : DepthSplit) ∈ original.nodes := included (by simp [DepthTree.nodes])
          have rootName : clip start ⟨a,cut,b⟩ = ⟨start,cut,b⟩ := by simp only [clip,max_eq_left lower]
          have rootBit : intervalUpdate request (preference original start memory) ⟨start,cut,b⟩ =
              intervalUpdate request (bits start memory) ⟨a,cut,b⟩ := by
            have lo : a ≤ request := lower.trans inSuffix
            simp only [intervalUpdate,inSuffix,lo,true_and,preference,original_of_cut original member,bits]
          have leftEq := ihl leftIncluded lower retained ⟨valid.1,keep⟩
          have rightEq := clip_updated_genuine original right rightIncluded start request (by omega) memory
          simp only [suffix,dif_pos retained,suffixSource,dif_pos keep,Source.mapRecords,
            ComparatorRecords.record,ComparatorRecords.value,rootName,rootBit,leftEq,rightEq]
        · simpa only [suffix,dif_pos retained,suffixSource,dif_neg keep] using
            clip_updated_suffix_genuine original right rightIncluded start request (by omega)
              memory d ⟨by omega,valid.2⟩
      · have keep : ¬d ≤ cut := by omega
        simpa only [suffix,dif_neg retained,suffixSource,dif_neg keep] using
          ihr rightIncluded (by omega) upper valid

theorem preference_splice_node {a b : Nat} (reference : DepthTree a b)
    (start d : Nat) (lo : a ≤ start) (hi : start ≤ b) (earlier : start ≤ d)
    (old incoming : DepthSplit → Bool) {split : DepthSplit}
    (member : split ∈ (suffix reference start lo hi).nodes) :
    preference reference start (spliceBits d old incoming) split =
      spliceBits d (preference reference start old) (preference reference start incoming) split := by
  obtain ⟨original,present,lookup,same⟩ := suffix_original_lookup reference start lo hi member
  have low : split.lo ≤ d ↔ original.lo ≤ d := by
    rw [← same]
    simp only [clip]
    omega
  by_cases before : original.lo ≤ d <;>
    simp only [preference,lookup,spliceBits,if_pos,if_neg,low,before]
  all_goals split <;> rfl

theorem prepared_splice_source {a b : Nat} (reference : DepthTree a b)
    (start d : Nat) (lo : a ≤ start) (hi : start ≤ b) (earlier : start ≤ d)
    (old incoming : DepthSplit → Bool) :
    source (suffix reference start lo hi)
      (spliceBits d (intervalUpdate d (preference reference start old))
        (intervalUpdate d (preference reference start incoming))) =
      source (suffix reference start lo hi)
        (intervalUpdate d (preference reference start (spliceBits d old incoming))) := by
  rw [update_splice]
  apply source_congr
  intro split member
  have same := preference_splice_node reference start d lo hi earlier old incoming member
  simp only [intervalUpdate,same]

/-- Expose a balanced separator and close both children. The marks and
interval names are ghost data, but every move and rotation is charged. -/
theorem expose_closed_erased (component : AuxiliaryComponent Nat Nat (Tagged Payload))
    (clean : Clean component.core) (marked : MarkedPorts component)
    (key : Nat) (found : searchResult key component.core = true) :
    SourcePointer.Rearranges (ComparatorRecords.erase (closed component))
      (.fork () (ComparatorRecords.erase (closed (cutLeft component key found)))
        (ComparatorRecords.erase (closed (cutRight component key found))))
      (5730 * Nat.clog 2 (component.core.size + 1) + 10) := by
  let pivot : Cached := (component.core.size,⟨key,(splitAt key component.core component.balanced found).value⟩)
  have first := (open_charged component clean marked).trans (expose_charged component key found)
  have left := (close_charged (cutLeft component key found)).left
    (r := (cutRight component key found).tree) (record := pivot)
  have right := (close_charged (cutRight component key found)).right
    (l := closed (cutLeft component key found)) (record := pivot)
  have run := ((first.trans left).trans right).mapRecords (fun _ => ())
  simpa only [ComparatorRecords.erase,Source.mapRecords] using run.mono (by omega)

/-- At an interior requested depth, the old suffix is detached from the
same prefix that subsequently receives the incoming suffix. Both traces
have literal erased endpoints; the prefix is never rebuilt. -/
theorem prepared_exchange_interior {a b : Nat} (reference : DepthTree a b)
    (start d : Nat) (lo : a ≤ start) (strict : start < d) (upper : d < b)
    (old incoming : DepthSplit → Bool)
    (component incomingTail : AuxiliaryComponent Nat Nat (Tagged Payload))
    (represented : Represents followsRight
      (suffixSource reference (intervalUpdate d (bits start old)) start ⟨lo,by omega⟩) component)
    (incomingRep : Represents followsRight
      (suffixSource reference (bits (d+1) incoming) (d+1) ⟨by omega,by omega⟩) incomingTail) :
    ∃ (kept : Source Nat Unit) (oldTail result : AuxiliaryComponent Nat Nat (Tagged Payload)),
      Represents followsRight
        (suffixSource reference (bits (d+1) old) (d+1) ⟨by omega,by omega⟩) oldTail ∧
      Represents followsRight
        (suffixSource reference (intervalUpdate d (bits start (spliceBits d old incoming)))
          start ⟨lo,by omega⟩) result ∧
      SourcePointer.Rearranges (ComparatorRecords.erase (closed component))
        (.fork () kept (.fork () (.leaf d ()) (ComparatorRecords.erase (closed oldTail))))
        (20000 * (Nat.clog 2 ((LocalReferences.depthReference reference).height + 1) + 1)) ∧
      SourcePointer.Rearranges
        (.fork () kept (.fork () (.leaf d ()) (ComparatorRecords.erase (closed incomingTail))))
        (ComparatorRecords.erase (closed result))
        (20000 * (Nat.clog 2 ((LocalReferences.depthReference reference).height + 1) + 1)) := by
  let induced := suffix reference start lo (by omega)
  let p := intervalUpdate d (preference reference start old)
  let q := intervalUpdate d (preference reference start incoming)
  let active := ComparatorRecords.component (clip start) component
  have activeRep := ComparatorRecords.represents (clip start) represented
  rw [clip_updated_source_of_subset reference reference (fun _ h => h)
    start d lo (by omega) (by omega) old] at activeRep
  have preparedP : (Secondary.decodeDepth induced p).terminal = d := by
    rw [Secondary.decodeDepth_access]
    exact PreferredProjection.PrefRouter.terminal_access d _
      ((Secondary.decodeDepth_mem induced _ d).mpr ⟨by omega,by omega⟩)
  have preparedQ : (Secondary.decodeDepth induced q).terminal = d := by
    rw [Secondary.decodeDepth_access]
    exact PreferredProjection.PrefRouter.terminal_access d _
      ((Secondary.decodeDepth_mem induced _ d).mpr ⟨by omega,by omega⟩)
  let found := prepared_lower_found induced p d preparedP strict active activeRep
  let left := cutLeft active (d-1) found
  let right := cutRight active (d-1) found
  have rightRep := prepared_cutRight_represents induced p d ⟨by omega,by omega⟩
    preparedP strict active activeRep found
  have restoredRight := ComparatorRecords.represents (originalName reference) rightRep
  rw [restore_updated_suffix_of_subset reference reference (fun _ h => h)
    start d d lo (by omega) (by omega) ⟨by omega,by omega⟩ old] at restoredRight
  obtain ⟨oldTail,boundary,_,oldTailRep,detach⟩ := detach_stable_charged
    reference start d (by omega) ⟨by omega,upper⟩ old
      (ComparatorRecords.component (originalName reference) right) restoredRight
  obtain ⟨pivot,attached,_,_,_,attachedRep,attach⟩ := attach_stable_charged
    reference start d (by omega) ⟨by omega,upper⟩ incoming incomingTail incomingRep
  have clippedIncoming := ComparatorRecords.represents (clip start) attachedRep
  rw [clip_updated_suffix_of_subset reference reference (fun _ h => h)
    start d d lo (by omega) (by omega) ⟨by omega,by omega⟩ incoming] at clippedIncoming
  obtain ⟨joined,joinedRep,join⟩ := prepared_join_charged induced p q d ⟨by omega,by omega⟩
    preparedP preparedQ strict active (ComparatorRecords.component (clip start) attached)
      activeRep clippedIncoming found active.core.size
  have restoredJoined := ComparatorRecords.represents (originalName reference) joinedRep
  rw [prepared_splice_source reference start d lo (by omega) (by omega) old incoming,
    restore_updated_source_of_subset reference reference (fun _ h => h)
      start d lo (by omega) (by omega) (spliceBits d old incoming)] at restoredJoined
  obtain ⟨clean,marked⟩ := activeRep.invariant
  have expose := expose_closed_erased active clean marked (d-1) found
  rw [ComparatorRecords.erase_component] at expose
  have detachErased := detach.mapRecords (fun _ => ())
  change SourcePointer.Rearranges (ComparatorRecords.erase (closed (ComparatorRecords.component (originalName reference) right)))
    (.fork () (.leaf d ()) (ComparatorRecords.erase (closed oldTail))) _ at detachErased
  rw [ComparatorRecords.erase_component] at detachErased
  have first := expose.trans (detachErased.right (l := ComparatorRecords.erase (closed left)) (record := ()))
  have attachErased := attach.mapRecords (fun _ => ())
  change SourcePointer.Rearranges (.fork () (.leaf d ()) (ComparatorRecords.erase (closed incomingTail)))
    (ComparatorRecords.erase (closed attached)) _ at attachErased
  have joinErased := join.mapRecords (fun _ => ())
  change SourcePointer.Rearranges (.fork () (ComparatorRecords.erase (closed left))
    (ComparatorRecords.erase (closed (ComparatorRecords.component (clip start) attached))))
    (ComparatorRecords.erase (closed joined)) _ at joinErased
  rw [ComparatorRecords.erase_component] at joinErased
  have second := (attachErased.right (l := ComparatorRecords.erase (closed left)) (record := ())).trans joinErased
  have size := represented_size induced p active activeRep
  have height := suffix_height reference start lo (by omega)
  have logSize := Nat.clog_monotone 2 (Nat.add_le_add_right (size.trans height) 1)
  have logHeight : Nat.clog 2 ((LocalReferences.depthReference induced).height + 1) ≤
      Nat.clog 2 ((LocalReferences.depthReference reference).height + 1) :=
    Nat.clog_monotone 2 (Nat.add_le_add_right height 1)
  refine ⟨ComparatorRecords.erase (closed left),oldTail,
    ComparatorRecords.component (originalName reference) joined,oldTailRep,restoredJoined,
    first.mono (by omega),?_⟩
  rw [ComparatorRecords.erase_component]
  exact second.mono (by omega)

end MultiSplay.ComparatorStableSuffix

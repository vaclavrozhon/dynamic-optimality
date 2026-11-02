import MultiSplay.ComparatorRecordTransport
import MultiSplay.ComparatorSuffixMemory
import ChaCha.Paper20261030.SuffixSource

/-! # The same suffix with persistent original interval names

Clipping changes the lower endpoint written in a structural interval's
name. The stable form retains the original reference interval instead.
Both forms have the same preference bits and physical gap tree. These
equalities connect the general induced-reference access to the existing
prepared suffix-cut lemmas without introducing or resetting an owner.
-/

namespace MultiSplay.ComparatorStableSuffix

open ChaCha
open Paper20261030
open ColoredStorage Auxiliary AuxiliaryComponent BoundaryObservations PathDecomposition
open SecondaryDecomposition
open ComparatorSuffix

def bits (start : Nat) (memory : DepthSplit → Bool) (split : DepthSplit) : Bool :=
  if split.lo < start then false else memory split

def originalName {a b : Nat} (reference : DepthTree a b) (split : DepthSplit) : DepthSplit :=
  if split.cut < split.hi then (reference.locate split.cut (split.cut+1)).getD split else split

theorem originalName_node {a b : Nat} (reference : DepthTree a b) {split : DepthSplit}
    (member : split ∈ reference.nodes) : originalName reference split = split := by
  simp only [originalName,if_pos (reference.node_bounds member).2.2.1,
    original_of_cut reference member,Option.getD_some]

theorem originalName_leaf {a b : Nat} (reference : DepthTree a b) (key : Nat) :
    originalName reference ⟨key,key,key⟩ = ⟨key,key,key⟩ := by
  simp only [originalName,Nat.lt_irrefl,if_false]

theorem clip_leaf (start key : Nat) (inside : start ≤ key) :
    clip start ⟨key,key,key⟩ = ⟨key,key,key⟩ := clip_genuine start _ inside

theorem map_source {a b : Nat} (reference : DepthTree a b) (rename : DepthSplit → DepthSplit)
    (before after : DepthSplit → Bool)
    (nodes : ∀ split ∈ reference.nodes, rename split = split ∧ before split = after split)
    (leaves : ∀ key, a ≤ key → key ≤ b → rename ⟨key,key,key⟩ = ⟨key,key,key⟩) :
    (source reference before).mapRecords (ComparatorRecords.record rename) = source reference after := by
  induction reference with
  | leaf a =>
      simp only [source,Source.mapRecords,ComparatorRecords.record,ComparatorRecords.value,leaves a le_rfl le_rfl]
  | @node a b cut ha hb left right ihl ihr =>
      obtain ⟨rootName,rootBit⟩ := nodes ⟨a,cut,b⟩ (by simp [DepthTree.nodes])
      have leftEq := ihl (fun split member => nodes split (by simp [DepthTree.nodes,member]))
        (fun key lo hi => leaves key lo (by omega))
      have rightEq := ihr (fun split member => nodes split (by simp [DepthTree.nodes,member]))
        (fun key lo hi => leaves key (by omega) hi)
      simp only [source,Source.mapRecords,ComparatorRecords.record,ComparatorRecords.value,
        rootName,rootBit,leftEq,rightEq]

theorem restore_genuine {x y a b : Nat} (original : DepthTree x y) (reference : DepthTree a b)
    (included : reference.nodes ⊆ original.nodes) (start : Nat) (lower : start ≤ a)
    (memory : DepthSplit → Bool) :
    (source reference (preference original start memory)).mapRecords
      (ComparatorRecords.record (originalName original)) = source reference (bits start memory) := by
  apply map_source
  · intro split member
    have genuine : start ≤ split.lo := lower.trans (reference.node_bounds member).1
    exact ⟨originalName_node original (included member),by
      rw [preference_genuine original start memory (included member) genuine]
      simp only [bits,if_neg (by omega : ¬split.lo < start)]⟩
  · intro key _ _
    exact originalName_leaf original key

theorem clip_genuine_source {x y a b : Nat} (original : DepthTree x y) (reference : DepthTree a b)
    (included : reference.nodes ⊆ original.nodes) (start : Nat) (lower : start ≤ a)
    (memory : DepthSplit → Bool) :
    (source reference (bits start memory)).mapRecords (ComparatorRecords.record (clip start)) =
      source reference (preference original start memory) := by
  apply map_source
  · intro split member
    have genuine : start ≤ split.lo := lower.trans (reference.node_bounds member).1
    exact ⟨clip_genuine start split genuine,by
      rw [preference_genuine original start memory (included member) genuine]
      simp only [bits,if_neg (by omega : ¬split.lo < start)]⟩
  · intro key lo _
    exact clip_leaf start key (lower.trans lo)

theorem restore_source_of_subset {x y a b : Nat} (original : DepthTree x y) (reference : DepthTree a b)
    (included : reference.nodes ⊆ original.nodes) (start : Nat) (lower : a ≤ start) (upper : start ≤ b)
    (memory : DepthSplit → Bool) :
    (source (suffix reference start lower upper) (preference original start memory)).mapRecords
      (ComparatorRecords.record (originalName original)) = suffixSource reference (bits start memory) start ⟨lower,upper⟩ := by
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
        have rootBit : preference original start memory ⟨start,cut,b⟩ = bits start memory ⟨a,cut,b⟩ := by
          simp only [preference,original_of_cut original member,bits]
        have leftEq := ihl leftIncluded lower retained
        have rightEq := restore_genuine original right rightIncluded start (by omega) memory
        simp only [suffix,dif_pos retained,source,Source.mapRecords,ComparatorRecords.record,
          ComparatorRecords.value,suffixSource,rootName,rootBit,leftEq,rightEq]
      · simpa only [suffix,suffixSource,dif_neg retained] using ihr rightIncluded (by omega) upper

theorem clip_source_of_subset {x y a b : Nat} (original : DepthTree x y) (reference : DepthTree a b)
    (included : reference.nodes ⊆ original.nodes) (start : Nat) (lower : a ≤ start) (upper : start ≤ b)
    (memory : DepthSplit → Bool) :
    (suffixSource reference (bits start memory) start ⟨lower,upper⟩).mapRecords
      (ComparatorRecords.record (clip start)) =
        source (suffix reference start lower upper) (preference original start memory) := by
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
        have rootBit : preference original start memory ⟨start,cut,b⟩ = bits start memory ⟨a,cut,b⟩ := by
          simp only [preference,original_of_cut original member,bits]
        have leftEq := ihl leftIncluded lower retained
        have rightEq := clip_genuine_source original right rightIncluded start (by omega) memory
        simp only [suffix,dif_pos retained,source,Source.mapRecords,ComparatorRecords.record,
          ComparatorRecords.value,suffixSource,rootName,rootBit,leftEq,rightEq]
      · simpa only [suffix,suffixSource,dif_neg retained] using ihr rightIncluded (by omega) upper

theorem restore_source {a b : Nat} (reference : DepthTree a b) (start : Nat)
    (lower : a ≤ start) (upper : start ≤ b) (memory : DepthSplit → Bool) :
    (source (suffix reference start lower upper) (preference reference start memory)).mapRecords
      (ComparatorRecords.record (originalName reference)) =
        suffixSource reference (bits start memory) start ⟨lower,upper⟩ :=
  restore_source_of_subset reference reference (fun _ h => h) start lower upper memory

theorem clip_source {a b : Nat} (reference : DepthTree a b) (start : Nat)
    (lower : a ≤ start) (upper : start ≤ b) (memory : DepthSplit → Bool) :
    (suffixSource reference (bits start memory) start ⟨lower,upper⟩).mapRecords
      (ComparatorRecords.record (clip start)) =
        source (suffix reference start lower upper) (preference reference start memory) :=
  clip_source_of_subset reference reference (fun _ h => h) start lower upper memory

end MultiSplay.ComparatorStableSuffix

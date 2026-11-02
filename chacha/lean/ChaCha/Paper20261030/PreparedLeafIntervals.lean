import ChaCha.Paper20261030.DecompositionLeaves
import ChaCha.Paper20261030.CanonicalRetainedPortFacts

set_option autoImplicit false

/-! Exact depth intervals of the blocks exposed by preparation. The
premise is the leaf word preserved by the executed source trace; the
location and disjointness of the blocks are conclusions. -/

namespace ChaCha.Paper20261030.PreparedLeafIntervals

open ColoredStorage Structural SecondaryDecomposition Auxiliary AuxiliaryComponent
open BoundaryObservations PathDecomposition

theorem split_range (a b d : Nat) (head tail : List Nat)
    (word : head ++ d::tail = List.range' a (b+1-a)) :
    head = List.range' a (d-a) ∧ tail = List.range' (d+1) (b-d) := by
  have length := congrArg List.length word
  simp only [List.length_append,List.length_cons,List.length_range'] at length
  have suffix := congrArg (List.drop head.length) word
  simp only [List.drop_left,List.drop_range',Nat.mul_one] at suffix
  obtain ⟨position,positive,rest⟩ := List.range'_eq_cons_iff.mp suffix.symm
  have initial := congrArg (List.take head.length) word
  rw [List.take_left,List.take_range'_of_length_ge (by omega)] at initial
  constructor
  · rw [show d-a = head.length by omega]
    exact initial
  · rw [show b+1-a-head.length-1 = b-d by omega] at rest
    exact rest

theorem suffix_range (a b d : Nat) (valid : a ≤ d ∧ d ≤ b) :
    (List.range' a (b+1-a)).filter (Secondary.suffixKeep d) = List.range' d (b+1-d) := by
  have split : List.range' a (b+1-a) = List.range' a (d-a) ++ List.range' d (b+1-d) := by
    have eq := List.range'_append_1 (s := a) (m := d-a) (n := b+1-d)
    simpa only [show a+(d-a) = d by omega,
      show d-a+(b+1-d) = b+1-a by omega] using eq.symm
  rw [split,List.filter_append]
  have before : (List.range' a (d-a)).filter (Secondary.suffixKeep d) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro key member
    simp only [List.mem_range'_1] at member
    simp only [Secondary.suffixKeep,decide_eq_true_eq]
    omega
  have after : (List.range' d (b+1-d)).filter (Secondary.suffixKeep d) = List.range' d (b+1-d) := by
    apply List.filter_eq_self.mpr
    intro key member
    simpa only [Secondary.suffixKeep,decide_eq_true_eq] using (List.mem_range'_1.mp member).1
  rw [before,after,List.nil_append]

theorem represented_active {η : Type*} {a b d : Nat}
    (reference : DepthTree a b) (preferences : DepthSplit → Bool)
    (component : AuxiliaryComponent Nat Nat (Tagged Payload))
    (represented : Represents followsRight (source reference preferences) component)
    (decorated : Source Nat (η × Cached))
    (erases : decorated.mapRecords Prod.snd = closed component)
    (head tail : Source Nat (η × Cached))
    (word : head.shape.leaves ++ d::tail.shape.leaves = decorated.shape.leaves) :
    head.shape.leaves = List.range' a (d-a) ∧ tail.shape.leaves = List.range' (d+1) (b-d) := by
  have erasedWord := congrArg (fun tree : Source Nat Cached => tree.shape.leaves) erases
  simp only [Source.mapRecords_shape] at erasedWord
  exact split_range a b d _ _ (word.trans (erasedWord.trans (represented_leaf_word reference preferences component represented)))

theorem represented_incoming {η : Type*} {a b d : Nat}
    (reference : DepthTree a b) (preferences : DepthSplit → Bool) (valid : a ≤ d ∧ d ≤ b)
    (component : AuxiliaryComponent Nat Nat (Tagged Payload))
    (represented : Represents followsRight (suffixSource reference preferences d valid) component)
    (decorated : Source Nat (η × Cached))
    (erases : decorated.mapRecords Prod.snd = closed component)
    (tail : Source Nat (η × Cached))
    (word : d::tail.shape.leaves = decorated.shape.leaves) :
    tail.shape.leaves = List.range' (d+1) (b-d) := by
  have erasedWord := congrArg (fun tree : Source Nat Cached => tree.shape.leaves) erases
  simp only [Source.mapRecords_shape] at erasedWord
  have entire := word.trans (erasedWord.trans
    (represented_suffix_leaf_word reference preferences d valid component represented))
  rw [suffix_range a b d valid] at entire
  have rest := (List.range'_eq_cons_iff.mp entire.symm).2.2
  rw [show b+1-d-1 = b-d by omega] at rest
  exact rest

theorem below {a d : Nat} {word : List Nat} (interval : word = List.range' a (d-a)) :
    ∀ key ∈ word, key < d := by
  intro key member
  rw [interval,List.mem_range'_1] at member
  omega

theorem above {b d : Nat} {word : List Nat} (interval : word = List.range' (d+1) (b-d)) :
    ∀ key ∈ word, d < key := by
  intro key member
  rw [interval,List.mem_range'_1] at member
  omega

end ChaCha.Paper20261030.PreparedLeafIntervals

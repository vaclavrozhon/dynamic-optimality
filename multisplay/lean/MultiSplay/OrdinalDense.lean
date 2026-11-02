import MultiSplay.OrdinalShape

/-! # Dense zero-based coordinates for any physical component interval -/

namespace MultiSplay.OrdinalShift

open Splay.Tree (BST)

theorem toRaw (offset : Nat) {lower upper : Nat} (source : BST lower upper) :
    DynamicOptimality.BST.toRaw (tree offset source) =
      Auxiliary.map (offset+·) (DynamicOptimality.BST.toRaw source) := by
  induction source <;> simp_all [tree, DynamicOptimality.BST.toRaw, Auxiliary.map]

end MultiSplay.OrdinalShift

namespace MultiSplay.Alphabet

open Splay.Tree (BST)
open ChaCha.MTR.Tree (inorder)

theorem exists_dense {lower upper : Nat} (source : BST lower upper) :
    ∃ dense : BST 0 source.size,
      Auxiliary.map (lower+·) (DynamicOptimality.BST.toRaw dense) = DynamicOptimality.BST.toRaw source := by
  obtain ⟨count, dense, interpretation, represented, cardinality⟩ := exists_encoding (DynamicOptimality.BST.toRaw source)
  rw [DynamicOptimality.BST.toRaw_size] at cardinality
  subst count
  have observed := congrArg inorder represented
  rw [map_inorder, indexed_inorder, BST.size_eq_upper, indexed_inorder] at observed
  have standard : (List.range' 0 source.size).map (lower+·) = List.range' lower source.size := by
    simpa only [Nat.add_zero] using (List.map_add_range' (a := lower) 0 source.size 1)
  have maps := observed.trans standard.symm
  have agree : ∀ key, 0 ≤ key → key < source.size → interpretation key = lower+key := by
    intro key _ inside
    exact List.map_inj_left.mp maps key (by simp [List.mem_range'_1, inside])
  exact ⟨dense, (indexed_congr dense agree).symm.trans represented⟩

/-- Shifting the dense tree back recovers the original indexed tree, not only
its inorder word or an equivalent cost. -/
theorem exists_unshift {lower upper : Nat} (source : BST lower upper) :
    ∃ count : Nat, ∃ dense : BST 0 count,
      lower+count = upper ∧ HEq (OrdinalShift.tree lower dense) source := by
  obtain ⟨dense, represented⟩ := exists_dense source
  generalize countEq : source.size = count at dense represented
  have bound : lower+count = upper := by have h := source.size_add_lower_eq_upper; omega
  subst upper
  have physical : DynamicOptimality.BST.toRaw (OrdinalShift.tree lower dense) = DynamicOptimality.BST.toRaw source :=
    (OrdinalShift.toRaw lower dense).trans represented
  have exactTree : OrdinalShift.tree lower dense = source := by
    apply indexed_eq_of_map_eq _ _ (fun key => key) (fun key => key)
    exact congrArg (Auxiliary.map (fun key => key)) physical
  exact ⟨count, dense, rfl, heq_of_eq exactTree⟩

end MultiSplay.Alphabet

import TangoSquared.Paper20261030.RobustBSTUpperBound
import DynamicOptimality.PointerRelabel
import DynamicOptimality.ConnectedPointer
import Mathlib.Data.List.Sort

/-! The new manuscript's robust rectangle bound and actual Tango-squared
trace now use the same attained offline optimum as the splay development.
The trace theorem is for power-of-two universes; it does not assert the
remaining bounded local online implementation. -/

namespace TangoSquared.Paper20261030

open DynamicOptimality

namespace Rectangles

theorem robustBound_le_shared_OPT {n : Nat} (requests : List (Fin n)) :
    robustBound (accessPoints (requests.map (fun key => (key.val : Int)))) ≤ 74*OPT requests := by
  obtain ⟨initial,final,cost,execution,bound⟩ := exists_pointer_of_OPT requests
  have mapped := Relabel.execution (fun key : Nat => (key : Int)) execution
  have ordered := Relabel.tree_ordered (fun key : Nat => (key : Int))
    (by intro x y smaller; change (x : Int) < (y : Int); exact_mod_cast smaller) (BST.toRaw_ordered initial)
  have lower := robustBound_le_pointer_cost mapped ordered
  simp only [List.map_map,Function.comp_def] at lower
  omega

end Rectangles

namespace Dyadic

theorem indexed_canonical_word {H : Nat} (before : BST 0 (2^H)) :
    (Relabel.tree (fun key : Nat => (key : Int)) before.toRaw).inorder = (canonical H 0).leaves := by
  have ordered := Relabel.tree_ordered (fun key : Nat => (key : Int))
    (by intro x y smaller; change (x : Int) < (y : Int); exact_mod_cast smaller) (BST.toRaw_ordered before)
  apply List.Pairwise.eq_of_mem_iff ordered (canonical_ordered H 0)
  intro key
  rw [Relabel.tree_word,List.mem_map,canonical_zero_mem]
  constructor
  · rintro ⟨original,member,rfl⟩
    obtain ⟨_,upper⟩ := BST.toRaw_mem before |>.mp member
    constructor
    · exact Int.natCast_nonneg _
    · exact_mod_cast upper
  · intro valid
    refine ⟨key.toNat,?_,Int.toNat_of_nonneg valid.1⟩
    apply (BST.toRaw_mem before).mpr
    refine ⟨Nat.zero_le _,?_⟩
    have castBound : (key.toNat : Int) < (2 : Int)^H := by
      rw [Int.toNat_of_nonneg valid.1]
      exact valid.2
    exact_mod_cast castBound

/-- Actual shared-model execution on the original natural keys, with
linear initialization charged and the common splay/Tango optimum. -/
theorem bst_run_shared_OPT {h : Nat} (before : BST 0 (2^(h+1)))
    (requests : List (Fin (2^(h+1)))) :
    ∃ (after : RawTree Nat) (cost : Nat), after.inorder = before.toRaw.inorder ∧ after.Ordered ∧
      PointerExecution before.toRaw (requests.map Fin.val) after cost ∧
      cost ≤ 11100000000*(OPT requests+2^(h+1))*(Nat.clog 2 (Nat.clog 2 (h+1)+2)+1) := by
  obtain ⟨competitor,final,competitorCost,competitorRun,competitorBound⟩ := exists_pointer_of_OPT requests
  let intKeys : List Int := requests.map (fun key => (key.val : Int))
  have keys : ∀ key ∈ intKeys, ValidKey (h+1) key := by
    intro key member
    obtain ⟨original,_,rfl⟩ := List.mem_map.mp member
    exact ⟨Int.natCast_nonneg _,by exact_mod_cast original.isLt⟩
  have mappedRun := Relabel.execution (fun key : Nat => (key : Int)) competitorRun
  simp only [List.map_map,Function.comp_def] at mappedRun
  have mappedOrdered := Relabel.tree_ordered (fun key : Nat => (key : Int))
    (by intro x y smaller; change (x : Int) < (y : Int); exact_mod_cast smaller) (BST.toRaw_ordered competitor)
  obtain ⟨intAfter,cost,word,_,run,bound⟩ := bst_versus_pointer _ (indexed_canonical_word before)
    intKeys keys mappedRun mappedOrdered
  have restored := Relabel.execution Int.toNat run
  have roundtrip := Relabel.tree_leftInverse (fun key : Nat => (key : Int)) Int.toNat
    (by intro key; exact Int.toNat_natCast key) before.toRaw
  have finalWord : (Relabel.tree Int.toNat intAfter).inorder = before.toRaw.inorder := by
    rw [Relabel.tree_word,word,Relabel.tree_word,List.map_map]
    simp only [Function.comp_def,Int.toNat_natCast]
    exact List.map_id _
  refine ⟨Relabel.tree Int.toNat intAfter,cost,finalWord,?_,?_,?_⟩
  · simpa only [MTR.Tree.Ordered,finalWord] using BST.toRaw_ordered before
  · simpa only [roundtrip,intKeys,List.map_map,Function.comp_def,Int.toNat_natCast] using restored
  · calc
      cost ≤ 300000000*(competitorCost+2^(h+1))*(Nat.clog 2 (Nat.clog 2 (h+1)+2)+1) := bound
      _ ≤ 300000000*(37*(OPT requests+2^(h+1)))*(Nat.clog 2 (Nat.clog 2 (h+1)+2)+1) :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (by
          rw [Nat.mul_add]
          exact Nat.add_le_add competitorBound (Nat.le_mul_of_pos_left _ (by decide))))
      _ = _ := by rw [← Nat.mul_assoc]

end Dyadic
end TangoSquared.Paper20261030

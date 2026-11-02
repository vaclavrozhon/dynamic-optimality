import DynamicOptimality.MultiFinger.Hand
import Mathlib.Data.List.Perm.Subperm

/-! A reduced hand retains every present finger, including when several
fingers share one key. Its size depends on the number of fingers, not on
the number of source vertices in their connecting paths. -/

namespace DynamicOptimality.MultiFinger.Steiner

open ChaCha.MTR

variable {α : Type*}

theorem merge_left_mem (marked : Bool) (left : RawTree α) (key : α) (right : RawTree α)
    {target : α} (member : target ∈ left.inorder) : target ∈ (merge marked left key right).inorder := by
  cases left <;> cases right <;> cases marked <;> simp_all [merge,present,Tree.inorder] <;> tauto

theorem merge_right_mem (marked : Bool) (left : RawTree α) (key : α) (right : RawTree α)
    {target : α} (member : target ∈ right.inorder) : target ∈ (merge marked left key right).inorder := by
  cases left <;> cases right <;> cases marked <;> simp_all [merge,present,Tree.inorder] <;> tauto

theorem retains (marked : α → Bool) (tree : RawTree α) {key : α}
    (member : key ∈ tree.inorder) (hit : marked key = true) :
    key ∈ (skeleton marked tree).inorder := by
  induction tree with
  | empty => simp [Tree.inorder] at member
  | node left pivot right ihl ihr =>
    simp only [Tree.inorder,List.mem_append,List.mem_singleton] at member
    change key ∈ (merge (marked pivot) (skeleton marked left) pivot (skeleton marked right)).inorder
    rcases member with (inside | equal) | inside
    · exact merge_left_mem _ _ _ _ (ihl inside)
    · subst pivot
      simp [merge,hit,Tree.inorder]
    · exact merge_right_mem _ _ _ _ (ihr inside)

theorem ordered [LinearOrder α] (marked : α → Bool) (tree : RawTree α)
    (valid : tree.Ordered) : (skeleton marked tree).Ordered :=
  valid.sublist (skeleton_word_sublist marked tree)

/-- Repeated finger positions are harmless: the reference has distinct
keys, so it counts each occupied position at most once. -/
theorem size_le_fingers [DecidableEq α] (fingers : List α) (tree : RawTree α)
    (distinct : tree.inorder.Nodup) :
    (skeleton (fun key => decide (key ∈ fingers)) tree).size ≤ 2*fingers.length := by
  have selected : (tree.inorder.filter (fun key => decide (key ∈ fingers))).Nodup := distinct.filter _
  have subset : tree.inorder.filter (fun key => decide (key ∈ fingers)) ⊆ fingers := by
    intro key member
    simpa using (List.mem_filter.mp member).2
  have length := (List.subperm_of_subset selected subset).length_le
  exact (size_le_marks _ tree).trans (Nat.mul_le_mul_left 2 length)

end DynamicOptimality.MultiFinger.Steiner

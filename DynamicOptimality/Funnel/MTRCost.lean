import DynamicOptimality.Funnel.MTRVisibility
import DynamicOptimality.Funnel.Counts
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card

/-!
# Source visibility edges are bounded by actual MTR search-node cost

The initial tree is arbitrary, and no universe-size initialization term is
charged. Cold keys may add ancestors; this is why the bound is an inequality.
-/

namespace DynamicOptimality.Funnel

open ChaCha.MTR ChaCha.MTR.Tree

variable {α : Type*} [LinearOrder α]

theorem successful_at (tree : Tree α) (word : List α) (success : Successful tree word)
    (p : Fin word.length) :
    ∃ depth, searchDepth (word.get p) (run tree (word.take p.val)) = some depth := by
  have suffix := ((successful_append tree (word.take p.val) (word.drop p.val)).mp
    (by simpa only [List.take_append_drop] using success)).2
  rw [List.drop_eq_getElem_cons p.isLt] at suffix
  exact suffix.1

theorem incoming_bound (tree : Tree α) (word : List α) (success : Successful tree word)
    (p : Fin word.length) :
    (incoming word.get Finset.univ p).card + 1 ≤
      (searchDepth (word.get p) (run tree (word.take p.val))).getD 0 + 1 := by
  classical
  let earlier := incoming word.get Finset.univ p
  let keys := earlier.image word.get
  let path := searchPath (word.get p) (run tree (word.take p.val))
  have distinct : Set.InjOn word.get earlier := by
    intro q hq r hr same
    exact (mem_incoming.mp hq).column_unique (mem_incoming.mp hr) same
  have keyCount : keys.card = earlier.card := Finset.card_image_iff.mpr distinct
  have currentNot : word.get p ∉ keys := by
    intro member
    obtain ⟨q,hq,same⟩ := Finset.mem_image.mp member
    exact (mem_incoming.mp hq).2.2.2.1 same
  obtain ⟨depth,successful⟩ := successful_at tree word success p
  have currentOn : word.get p ∈ path := by
    have last := searchPath_last_of_success (word.get p) (run tree (word.take p.val)) depth successful
    exact List.mem_of_getLast? last
  have included : insert (word.get p) keys ⊆ path.toFinset := by
    intro key member
    rcases Finset.mem_insert.mp member with same | earlierKey
    · exact List.mem_toFinset.mpr (same ▸ currentOn)
    · obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp earlierKey
      exact List.mem_toFinset.mpr ((mem_incoming.mp hq).mem_mtr_path tree success)
  have bound := (Finset.card_le_card included).trans (List.toFinset_card_le path)
  rw [Finset.card_insert_of_notMem currentNot,keyCount] at bound
  have pathLength := searchPath_length_of_success (word.get p) (run tree (word.take p.val)) depth successful
  simpa only [earlier,successful,Option.getD_some,path,pathLength] using bound

theorem runCost_eq_sum (tree : Tree α) (word : List α) :
    runCost tree word = ∑ p : Fin word.length,
      ((searchDepth (word.get p) (run tree (word.take p.val))).getD 0 + 1) := by
  induction word generalizing tree with
  | nil => simp [runCost]
  | cons x xs ih =>
    rw [runCost,ih]
    simp [Fin.sum_univ_succ,run,List.get_eq_getElem]

/-- Every visible edge has a distinct searched key, and every request also
pays for its searched key itself. This is the exact baseline convention. -/
theorem edges_add_length_le_mtrCost (tree : Tree α) (word : List α)
    (success : Successful tree word) :
    wordEdgeCount word + word.length ≤ runCost tree word := by
  rw [wordEdgeCount,edgeCount_eq_sum,runCost_eq_sum]
  have bound := Finset.sum_le_sum (fun (p : Fin word.length) (_ : p ∈ Finset.univ) =>
    incoming_bound tree word success p)
  simpa only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
    smul_eq_mul,Nat.mul_one] using bound

end DynamicOptimality.Funnel

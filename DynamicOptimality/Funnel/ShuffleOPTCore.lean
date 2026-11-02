import DynamicOptimality.Funnel.Interleave
import DynamicOptimality.Funnel.MTRSupersequence
import DynamicOptimality.Funnel.Relabel

/-! # Reducing the shared-OPT shuffle theorem to subsequence monotonicity

This module isolates the final numerical composition. The subsequence bound
is an explicit hypothesis here; the public endpoint must instantiate it with
its proved geometric monotonicity theorem.
-/

namespace DynamicOptimality.Funnel

variable {α β : Type*} [LinearOrder α] [LinearOrder β]

theorem Interleave.map {X Y W : List α} (interleave : Interleave X Y W) (f : α → β) :
    Interleave (X.map f) (Y.map f) (W.map f) := by
  induction interleave with
  | nil => exact .nil
  | left x _ ih => exact .left (f x) ih
  | right x _ ih => exact .right (f x) ih

theorem wordCount_map (word : List α) (keys : α ↪o β) :
    wordCount (word.map keys) = wordCount word := by
  let iso : Fin word.length ≃o Fin (word.map keys).length :=
    Fin.castOrderIso (by simp)
  let times := iso.toOrderEmbedding
  have image : Finset.univ.image times = Finset.univ := by
    ext p
    simp only [Finset.mem_image,Finset.mem_univ,true_and,iff_true]
    obtain ⟨q,rfl⟩ := iso.surjective p
    exact ⟨q,rfl⟩
  have functions : (word.map keys).get ∘ times = keys ∘ word.get := by
    funext p
    simp [List.get_eq_getElem,List.getElem_map,times,iso,Fin.castOrderIso]
  have reindexed := count_reindex (word.map keys).get times Finset.univ
  rw [image,functions] at reindexed
  exact reindexed.trans (count_relabel word.get keys Finset.univ)

/-- All tree and cost hypotheses have been discharged. Only the separately
proved geometric subsequence theorem remains explicit in this composition. -/
theorem interleave_OPT_bound_of_subsequence_bound
    (subsequenceBound : ∀ (small large : List Nat), small.Sublist large →
      wordCount small ≤ 4 * wordCount large + 8 * large.length)
    {n : Nat} {X Y W : List (Fin n)} (interleave : Interleave X Y W) :
    wordCount W + W.length ≤ 360639 * (DynamicOptimality.OPT X + DynamicOptimality.OPT Y) := by
  obtain ⟨leftTree,expandedX,leftSub,_,leftCost,leftSuccess⟩ := MTRSimulation.shared_OPT_supersequence X
  obtain ⟨rightTree,expandedY,rightSub,_,rightCost,rightSuccess⟩ := MTRSimulation.shared_OPT_supersequence Y
  obtain ⟨expandedW,expandedShuffle,retained⟩ := (interleave.map Fin.val).expand leftSub rightSub
  have mono := subsequenceBound (W.map Fin.val) expandedW retained
  have expanded := expandedShuffle.mtr_bound leftTree rightTree leftSuccess rightSuccess
  have length := retained.length_le
  have relabel := wordCount_map W (Fin.valOrderEmb n)
  change wordCount (W.map Fin.val) = wordCount W at relabel
  rw [relabel] at mono
  simp only [List.length_map] at length
  omega

end DynamicOptimality.Funnel

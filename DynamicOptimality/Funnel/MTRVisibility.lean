import DynamicOptimality.Funnel.Basic
import ChaCha.ExecutionFacts

/-! # Every geometrically visible occurrence is visited by actual MTR -/

namespace DynamicOptimality.Funnel

open ChaCha.MTR ChaCha.MTR.Tree

variable {α : Type*} [LinearOrder α]

theorem Visible.mem_mtr_path {word : List α} {p q : Fin word.length}
    (visible : Visible word.get Finset.univ p q) (tree : Tree α)
    (success : Successful tree word) :
    word.get q ∈ searchPath (word.get p) (run tree (word.take p.val)) := by
  let before := word.take q.val
  let between := (word.take p.val).drop (q.val+1)
  have qp : q.val < p.val := visible.2.2.1
  have split : word.take p.val = before ++ word.get q :: between := by
    have decomposition := List.take_append_drop (q.val+1) (word.take p.val)
    rw [List.take_take, Nat.min_eq_left (by omega),List.take_succ_eq_append_getElem q.isLt] at decomposition
    simpa only [before,between,List.get_eq_getElem,List.append_assoc,List.singleton_append] using decomposition.symm
  have prefixSuccess : Successful tree (word.take p.val) :=
    ((successful_append tree (word.take p.val) (word.drop p.val)).mp
      (by simpa only [List.take_append_drop] using success)).1
  have segmentSuccess : Successful (run tree before) (word.get q :: between) :=
    ((successful_append tree before (word.get q :: between)).mp (split ▸ prefixSuccess)).2
  have outside : ∀ z ∈ between, z < min (word.get p) (word.get q) ∨
      max (word.get p) (word.get q) < z := by
    intro z hz
    obtain ⟨k,hk,hz⟩ := List.mem_iff_getElem.mp hz
    have bound : q.val+1+k < p.val := by
      simp only [between,List.length_drop,List.length_take] at hk
      omega
    let s : Fin word.length := ⟨q.val+1+k,by omega⟩
    have qs : q < s := by change q.val < q.val+1+k; omega
    have sp : s < p := bound
    have key : word.get s = z := by
      simpa only [between,List.getElem_drop,List.getElem_take,List.get_eq_getElem,s] using hz
    have notBetween : ¬ Between (word.get p) (word.get q) z := by
      intro h
      exact visible.2.2.2.2 s (Finset.mem_univ _) qs sp
        ((between_comm _ _ _).mp (by simpa only [key] using h))
    by_cases lower : z < min (word.get p) (word.get q)
    · exact Or.inl lower
    · exact Or.inr (lt_of_not_ge (fun upper =>
        notBetween ((between_iff_min_max _ _ _).mpr ⟨le_of_not_gt lower,upper⟩)))
  rw [split,run_append]
  exact last_between_query_visited (word.get p) (word.get q) (run tree before) between
    segmentSuccess outside

end DynamicOptimality.Funnel

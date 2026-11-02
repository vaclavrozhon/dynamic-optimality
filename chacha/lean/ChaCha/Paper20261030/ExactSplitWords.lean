import ChaCha.Paper20261030.ComponentBoundary

/-!
# Identifying the exact record slices produced by a split

In a strictly separator-ordered word, an occurrence of a given separator
uniquely determines both surrounding words and its full payload. Hence
the physical balanced split recovers the specified semantic slices,
not merely sets of keys.
-/

namespace ChaCha.Paper20261030.Auxiliary

open Std Std.DTreeMap.Internal Std.DTreeMap.Internal.Impl

variable {β : Nat → Type*}

theorem separator_decomposition_unique (before after before' after' : List (Sigma β))
    (pivot pivot' : Sigma β)
    (ordered : (before ++ pivot :: after).Pairwise (fun a b => a.1 < b.1))
    (same : before ++ pivot :: after = before' ++ pivot' :: after') (key : pivot.1 = pivot'.1) :
    before = before' ∧ pivot = pivot' ∧ after = after' := by
  induction before generalizing before' with
  | nil =>
    cases before' with
    | nil =>
      have h := List.cons.inj same
      exact ⟨rfl,h.1,h.2⟩
    | cons first rest =>
      have hs := List.cons.inj same
      have hm : pivot' ∈ after := by rw [hs.2]; simp
      have hlt := (List.pairwise_cons.mp ordered).1 pivot' hm
      omega
  | cons first rest ih =>
    cases before' with
    | nil =>
      have hs := List.cons.inj same
      have hm : pivot ∈ rest ++ pivot :: after := by simp
      have hlt := (List.pairwise_cons.mp ordered).1 pivot hm
      rw [hs.1] at hlt
      omega
    | cons first' rest' =>
      have hs := List.cons.inj same
      have htail := (List.pairwise_cons.mp ordered).2
      obtain ⟨hb,hp,ha⟩ := ih rest' htail hs.2
      exact ⟨by rw [hs.1,hb],hp,ha⟩

theorem splitAt_word_decomposition (t : Impl Nat β) (balanced : t.Balanced) (ordered : t.Ordered)
    (before after : List (Sigma β)) (pivot : Sigma β)
    (word : t.toListModel = before ++ pivot :: after) (found : searchResult pivot.1 t = true) :
    (splitAt pivot.1 t balanced found).left.toListModel = before ∧
      (⟨pivot.1,(splitAt pivot.1 t balanced found).value⟩ : Sigma β) = pivot ∧
      (splitAt pivot.1 t balanced found).right.toListModel = after := by
  have hs := splitAt_toList pivot.1 t balanced found
  have ho := splitAt_ordered pivot.1 t balanced found ordered
  change ((splitAt pivot.1 t balanced found).left.toListModel ++
    ⟨pivot.1,(splitAt pivot.1 t balanced found).value⟩ ::
      (splitAt pivot.1 t balanced found).right.toListModel).Pairwise _ at ho
  have ho' := ho.imp (fun h => Nat.compare_eq_lt.mp h)
  exact separator_decomposition_unique _ _ before after _ pivot ho' (hs.trans word) rfl

theorem word_pivot_found (t : Impl Nat β) (ordered : t.Ordered)
    (before after : List (Sigma β)) (pivot : Sigma β)
    (word : t.toListModel = before ++ pivot :: after) : searchResult pivot.1 t = true := by
  rw [searchResult_eq_contains,contains_eq_containsKey ordered]
  apply Std.Internal.List.containsKey_of_mem
  rw [word]
  simp

end ChaCha.Paper20261030.Auxiliary

import ChaCha.BSTExecution
import ChaCha.HistoryCoherence
import ChaCha.PointerModel

/-!
# A cheap closed normalized supersequence

Every marked shallow rotation is replaced by the actual ambient-normalized
Move-to-Root tour. Marked accesses are retained explicitly, so the original word
is a sublist of the constructed word. Closure uses reverse shallow rotations.
-/

namespace ChaCha.MTR
open Tree Primary

theorem MarkedTrace.normalized_simulation {H : Nat} {t u : Tree Key} {xs : List Key}
    {k : Nat} (h : MarkedTrace t xs u k) (hord : Ordered t)
    (hleaves : ∀ x ∈ inorder t, x.length = H) :
    ∃ zs : List Key, xs.Sublist zs ∧ run t zs = u ∧
      runCost t zs ≤ 15 * k + xs.length ∧ AmbientNormalized H t zs ∧
      Successful t zs ∧ ∀ x ∈ zs, x.length = H := by
  induction h with
  | nil t => exact ⟨[], .refl _, rfl, by simp [runCost], trivial, trivial, by simp⟩
  | @rotate t u v xs k step rest ih =>
    have huo : Ordered u := by unfold Ordered; rw [← step.inorder_eq]; exact hord
    have hul : ∀ x ∈ inorder u, x.length = H := by
      intro x hx
      exact hleaves x (step.inorder_eq ▸ hx)
    obtain ⟨qs, hend, hc, hn, hs, hl⟩ := restrictedStep_normalized_simulation step hord hleaves
    obtain ⟨rs, hsub, hend', hc', hn', hs', hl'⟩ := ih huo hul
    refine ⟨qs ++ rs, hsub.trans (List.sublist_append_right _ _), ?_, ?_, ?_, ?_, ?_⟩
    · rw [run_append, hend, hend']
    · rw [runCost_append, hend]
      omega
    · apply (ambientNormalized_append H t qs rs).mpr
      exact ⟨hn, hend.symm ▸ hn'⟩
    · apply (successful_append t qs rs).mpr
      exact ⟨hs, hend.symm ▸ hs'⟩
    · intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact hl x hx
      · exact hl' x hx
  | @serve t v x xs k at_root rest ih =>
    obtain ⟨rs, hsub, hend, hc, hn, hs, hl⟩ := ih hord hleaves
    have hm : moveToRoot x t = t := by
      cases t with
      | empty => simp [rootKey] at at_root
      | node l a r => simp only [rootKey, Option.some.injEq] at at_root; subst a; exact moveToRoot_root l r x
    have hd : searchDepth x t = some 0 := by
      cases t with
      | empty => simp [rootKey] at at_root
      | node l a r => simp only [rootKey, Option.some.injEq] at at_root; subst a; exact searchDepth_root l r x
    have hx : x.length = H := by
      apply hleaves x
      cases t with
      | empty => simp [rootKey] at at_root
      | node l a r => simp only [rootKey, Option.some.injEq] at at_root; subst a; simp [inorder]
    have hnorm : NormalizedAt H t x := by
      intro a ha b hb hflip
      exact (hflip (by rw [hm])).elim
    refine ⟨x :: rs, hsub.cons_cons x, ?_, ?_, ?_, ?_, ?_⟩
    · simpa only [run, List.foldl_cons, hm] using hend
    · simp only [runCost, hd, Option.getD_some, Nat.zero_add, hm, List.length_cons]
      omega
    · exact ⟨hnorm, hm.symm ▸ hn⟩
    · exact ⟨⟨0, hd⟩, hm.symm ▸ hs⟩
    · intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact hx
      · exact hl y hy

/-- Concrete simulation theorem for arbitrary-root rooted-hull BST executions.
The constant is loose; no universe-size initialization cost is charged. -/
theorem AccessExecution.closed_normalized_supersequence {H : Nat} {t u : Tree Key}
    {xs : List Key} {cost : Nat} (h : AccessExecution t xs u cost) (hord : Ordered t)
    (hleaves : ∀ x ∈ inorder t, x.length = H) :
    ∃ zs : List Key, xs.Sublist zs ∧ run t zs = t ∧ runCost t zs ≤ 361 * cost ∧
      AmbientNormalized H t zs ∧ Successful t zs ∧ ∀ x ∈ zs, x.length = H := by
  obtain ⟨k, hk, ht⟩ := h.closed_marked_trace hord
  obtain ⟨zs, hsub, hend, hc, hn, hs, hl⟩ := ht.normalized_simulation hord hleaves
  have hlen := h.length_le_cost
  exact ⟨zs, hsub, hend, by omega, hn, hs, hl⟩

/-- The same concrete normalized-supersequence theorem for ordinary root-starting
BST pointer executions, including arbitrary local rotations and final roots. -/
theorem Pointer.Execution.closed_normalized_supersequence {H : Nat} {t u : Tree Key}
    {xs : List Key} {cost : Nat} (h : Pointer.Execution t xs u cost) (hord : Ordered t)
    (hleaves : ∀ x ∈ inorder t, x.length = H) :
    ∃ zs : List Key, xs.Sublist zs ∧ run t zs = t ∧ runCost t zs ≤ 361 * cost ∧
      AmbientNormalized H t zs ∧ Successful t zs ∧ ∀ x ∈ zs, x.length = H := by
  obtain ⟨hc, hle, hhull⟩ := h.toAccessExecution
  obtain ⟨zs, hsub, hend, hcost, hn, hs, hl⟩ :=
    hhull.closed_normalized_supersequence hord hleaves
  exact ⟨zs, hsub, hend, by omega, hn, hs, hl⟩

end ChaCha.MTR

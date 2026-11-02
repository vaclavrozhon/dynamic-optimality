import ChaCha.Paper20261030.DepthPreferences

/-!
# Forced sentinel preferences and the dormant boundary

The sentinel is the least participating depth. Intervals containing it
have structural preferences pointing toward it. Intervals strictly beyond
it keep their genuine memory bits. Decoding this rule and pruning to the
participating suffix produces a legal state whose endpoint is the sentinel.
-/

namespace ChaCha.Paper20261030.Secondary

open PreferredProjection

def suffixKeep (sentinel : Nat) (d : Nat) : Bool := decide (sentinel ≤ d)

theorem reference_bounds {a b : Nat} (reference : DepthTree a b) : a ≤ b := by
  cases reference <;> omega

theorem suffix_prune_nonempty {a b : Nat} (reference : DepthTree a b)
    (preference : DepthSplit → Bool) (sentinel : Nat) :
    (decodeDepth reference preference).prune (suffixKeep sentinel) ≠ none ↔ sentinel ≤ b := by
  constructor
  · intro hn
    cases hp : (decodeDepth reference preference).prune (suffixKeep sentinel) with
    | none => exact False.elim (hn hp)
    | some t =>
      have hm := t.terminal_mem
      rw [PrefRouter.prune_some_leaves (suffixKeep sentinel) hp] at hm
      obtain ⟨hm,hkeep⟩ := List.mem_filter.mp hm
      have hb := (decodeDepth_mem reference preference t.terminal).mp hm
      simp only [suffixKeep,decide_eq_true_eq] at hkeep
      omega
  · intro hs hn
    have hb : b ∈ (decodeDepth reference preference).leaves :=
      (decodeDepth_mem reference preference b).mpr ⟨reference_bounds reference,le_rfl⟩
    obtain ⟨t,ht,_⟩ := PrefRouter.prune_exists_of_retained (suffixKeep sentinel) hb (by simp [suffixKeep,hs])
    rw [hn] at ht
    contradiction

theorem sentinel_state_legal {a b : Nat} (reference : DepthTree a b)
    (preference : DepthSplit → Bool) (sentinel : Nat) :
    (decodeDepth reference (intervalUpdate sentinel preference)).Legal (suffixKeep sentinel) := by
  induction reference with
  | leaf a => trivial
  | @node a b c ha hb l r ihl ihr =>
    refine ⟨ihl,ihr,?_,?_⟩
    · intro hleft hright
      have hs := (suffix_prune_nonempty r (intervalUpdate sentinel preference) sentinel).mp hright
      have hc : ¬sentinel ≤ c := by
        intro hh
        exact (suffix_prune_nonempty l (intervalUpdate sentinel preference) sentinel).mpr hh hleft
      simp [intervalUpdate,show a ≤ sentinel ∧ sentinel ≤ b by omega,show c < sentinel by omega]
    · intro hright hleft
      have hs := (suffix_prune_nonempty l (intervalUpdate sentinel preference) sentinel).mp hleft
      exact False.elim ((suffix_prune_nonempty r (intervalUpdate sentinel preference) sentinel).mpr
        (by omega) hright)

theorem sentinel_state_terminal {a b : Nat} (reference : DepthTree a b)
    (preference : DepthSplit → Bool) (sentinel : Nat) (hs : a ≤ sentinel ∧ sentinel ≤ b) :
    (decodeDepth reference (intervalUpdate sentinel preference)).terminal = sentinel := by
  rw [decodeDepth_access]
  exact PrefRouter.terminal_access sentinel _ ((decodeDepth_mem reference preference sentinel).mpr hs)

theorem sentinel_pruned_terminal {a b : Nat} (reference : DepthTree a b)
    (preference : DepthSplit → Bool) (sentinel : Nat) (hs : a ≤ sentinel ∧ sentinel ≤ b)
    {t : PrefRouter Nat}
    (ht : (decodeDepth reference (intervalUpdate sentinel preference)).prune (suffixKeep sentinel) = some t) :
    t.terminal = sentinel := by
  have he := sentinel_state_terminal reference preference sentinel hs
  have hp := PrefRouter.terminal_of_prune_eq_some (suffixKeep sentinel)
    (decodeDepth reference (intervalUpdate sentinel preference)) t (by simp [he,suffixKeep]) ht
  exact hp.trans he

/-- Active intervals strictly beyond the boundary retain their actual
memory; forcing the sentinel path initializes no genuine memory bit. -/
theorem sentinel_preserves_genuine (preference : DepthSplit → Bool) (sentinel : Nat)
    (s : DepthSplit) (hs : sentinel < s.lo) : intervalUpdate sentinel preference s = preference s := by
  simp [intervalUpdate,show ¬s.lo ≤ sentinel by omega]

theorem sentinel_forces_boundary (preference : DepthSplit → Bool) (sentinel : Nat)
    (s : DepthSplit) (hs : s.lo ≤ sentinel ∧ sentinel ≤ s.hi) :
    intervalUpdate sentinel preference s = decide (s.cut < sentinel) := by simp [intervalUpdate,hs]

end ChaCha.Paper20261030.Secondary

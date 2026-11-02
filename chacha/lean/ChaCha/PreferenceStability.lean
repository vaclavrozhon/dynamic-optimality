import ChaCha.FlipAccounting

/-!
# Coupling two preference histories

When the same statically addressed writes are fed to two bit states, each
initial disagreement can change the flip decision only at its first write.
This is the state-potential part of the edit-stability argument for further
nesting. It does not assert subsequence preservation of emitted histories.
-/

namespace ChaCha.PreferenceStability

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

abbrev State (ι : Type*) := ι → Bool

def differing (s t : State ι) : Finset ι :=
  Finset.univ.filter fun i => s i ≠ t i

def hamming (s t : State ι) : Nat := (differing s t).card

def write (s : State ι) (i : ι) (b : Bool) : State ι := Function.update s i b

theorem differing_write_both (s t : State ι) (i : ι) (b : Bool) :
    differing (write s i b) (write t i b) = (differing s t).erase i := by
  ext j
  by_cases h : j = i
  · subst j
    simp [differing, write]
  · simp [differing, write, h]

/-- The disagreement potential pays exactly for unequal flip decisions. -/
theorem hamming_write_both (s t : State ι) (i : ι) (b : Bool) :
    hamming (write s i b) (write t i b) + edgeChange (s i) (t i) =
      hamming s t := by
  unfold hamming
  rw [differing_write_both]
  by_cases h : s i = t i
  · have hn : i ∉ differing s t := by simp [differing, h]
    simp [Finset.erase_eq_of_notMem hn, edgeChange, h]
  · have hm : i ∈ differing s t := by simp [differing, h]
    simpa [edgeChange, h] using Finset.card_erase_add_one hm

/-- Whether one write changes its addressed bit. -/
def flips (s : State ι) (i : ι) (b : Bool) : Bool := decide (s i ≠ b)

omit [Fintype ι] [DecidableEq ι] in
theorem flip_decision_disagreement (s t : State ι) (i : ι) (b : Bool) :
    edgeChange (flips s i b) (flips t i b) = edgeChange (s i) (t i) := by
  unfold flips
  cases hs : s i <;> cases ht : t i <;> cases b <;> decide

def run (s : State ι) : List (ι × Bool) → State ι
  | [] => s
  | (i, b) :: ws => run (write s i b) ws

/-- Number of positions whose emitted-flip decisions differ in two scans of
the same write stream. Common emitted events retain their common annotations. -/
def decisionDisagreements (s t : State ι) : List (ι × Bool) → Nat
  | [] => 0
  | (i, b) :: ws =>
      edgeChange (flips s i b) (flips t i b) +
        decisionDisagreements (write s i b) (write t i b) ws

theorem disagreement_accounting (s t : State ι) (ws : List (ι × Bool)) :
    decisionDisagreements s t ws + hamming (run s ws) (run t ws) = hamming s t := by
  induction ws generalizing s t with
  | nil => simp [decisionDisagreements, run]
  | cons w ws ih =>
    rcases w with ⟨i, b⟩
    have h := ih (write s i b) (write t i b)
    have hw := hamming_write_both s t i b
    simp only [decisionDisagreements, run, flip_decision_disagreement]
    omega

theorem decisionDisagreements_le_initial_hamming (s t : State ι)
    (ws : List (ι × Bool)) : decisionDisagreements s t ws ≤ hamming s t := by
  have h := disagreement_accounting s t ws
  omega

/-- Writing at most one address per list entry changes at most that many
initial bits. Repeated addresses only improve the estimate. -/
theorem differing_run_subset (s : State ι) (ws : List (ι × Bool)) :
    differing s (run s ws) ⊆ (ws.map Prod.fst).toFinset := by
  intro i hi
  by_contra hn
  have hi' : s i ≠ run s ws i := by simpa [differing] using hi
  have hsame : run s ws i = s i := by
    have hnot : ∀ w ∈ ws, w.1 ≠ i := by
      simpa only [List.mem_toFinset, List.mem_map, not_exists, not_and] using hn
    clear hi hi' hn
    induction ws generalizing s with
    | nil => rfl
    | cons w ws ih =>
      rcases w with ⟨j, b⟩
      have hji : j ≠ i := hnot (j, b) (by simp)
      have htail : ∀ w ∈ ws, w.1 ≠ i := by
        intro w hw
        exact hnot w (by simp [hw])
      simpa [run, write, Ne.symm hji] using ih (write s j b) htail
  exact hi' hsame.symm

theorem hamming_run_le_length (s : State ι) (ws : List (ι × Bool)) :
    hamming s (run s ws) ≤ ws.length := by
  have h := Finset.card_le_card (differing_run_subset s ws)
  have h' := List.toFinset_card_le (ws.map Prod.fst)
  simpa only [List.length_map, hamming] using h.trans h'

/-- If one input block is omitted, the later common write stream has at most
as many altered flip decisions as there were writes in the omitted block. -/
theorem omitted_block_suffix_disagreements (s : State ι)
    (omitted suffix : List (ι × Bool)) :
    decisionDisagreements s (run s omitted) suffix ≤ omitted.length :=
  (decisionDisagreements_le_initial_hamming s (run s omitted) suffix).trans
    (hamming_run_le_length s omitted)

end ChaCha.PreferenceStability

import ChaCha.Paper20261030.SplayAuxiliaryGlobalComponents

/-!
# Lifting two-component amortization to the entire endpoint table

The potential sums every actual auxiliary in every primary component.
The finite endpoint set is the original key set. The exact replacement
identity below cancels unchanged entries, including all dormant components.
-/

namespace ChaCha.Paper20261030.SplayAuxiliary.Global

open PreferredProjection

variable {α : Type*} [DecidableEq α]

def Table.potential (keys : Finset α) (components : Table α) : Nat :=
  keys.sum (fun key => (components key).potential)

theorem Table.potential_update (keys : Finset α) (components : Table α) (key : α)
    (member : key ∈ keys) (fresh : Component) :
    Table.potential keys (Function.update components key fresh) + (components key).potential =
      components.potential keys + fresh.potential := by
  have first := Finset.sum_erase_add (s := keys) (fun other => (components other).potential) member
  have second := Finset.sum_erase_add (s := keys)
    (fun other => (Function.update components key fresh other).potential) member
  have retained : (keys.erase key).sum (fun other => (Function.update components key fresh other).potential) =
      (keys.erase key).sum (fun other => (components other).potential) := by
    apply Finset.sum_congr rfl
    intro other present
    rw [Function.update_of_ne (Finset.mem_erase.mp present).1]
  rw [retained,Function.update_self] at second
  unfold Table.potential
  omega

theorem Table.single_amortized (keys : Finset α) (components : Table α) (key : α)
    (member : key ∈ keys) (fresh : Component) {rotations budget : Nat}
    (localBound : rotations+2*fresh.potential ≤ 2*(components key).potential+budget) :
    rotations+2*Table.potential keys (Function.update components key fresh) ≤
      2*components.potential keys+budget := by
  have cancellation := Table.potential_update keys components key member fresh
  omega

theorem Table.single_weighted_amortized (coefficient : Nat) (keys : Finset α)
    (components : Table α) (key : α) (member : key ∈ keys) (fresh : Component)
    {rotations budget : Nat}
    (localBound : rotations+coefficient*fresh.potential ≤ coefficient*(components key).potential+budget) :
    rotations+coefficient*Table.potential keys (Function.update components key fresh) ≤
      coefficient*components.potential keys+budget := by
  have scaled := congrArg (fun value => coefficient*value)
    (Table.potential_update keys components key member fresh)
  simp only [Nat.mul_add] at scaled
  omega

theorem Table.potential_pair (keys : Finset α) (components : Table α) (old fresh : α)
    (oldMem : old ∈ keys) (freshMem : fresh ∈ keys) (different : old ≠ fresh) :
    components.potential keys = (components old).potential + (components fresh).potential +
      components.potential ((keys.erase old).erase fresh) := by
  have first := Finset.sum_erase_add (s := keys) (fun key => (components key).potential) oldMem
  have second := Finset.sum_erase_add (s := keys.erase old) (fun key => (components key).potential)
    (Finset.mem_erase.mpr ⟨different.symm,freshMem⟩)
  unfold Table.potential
  rw [← first,← second]
  omega

theorem Table.potential_update_pair (keys : Finset α) (components : Table α) (old fresh : α)
    (oldMem : old ∈ keys) (freshMem : fresh ∈ keys) (different : old ≠ fresh)
    (dormant active : Component) :
    Table.potential keys (Function.update (Function.update components old dormant) fresh active) +
        (components old).potential + (components fresh).potential =
      components.potential keys + dormant.potential + active.potential := by
  let next : Table α := Function.update (Function.update components old dormant) fresh active
  have retained : next.potential ((keys.erase old).erase fresh) =
      components.potential ((keys.erase old).erase fresh) := by
    apply Finset.sum_congr rfl
    intro key member
    obtain ⟨notFresh,member⟩ := Finset.mem_erase.mp member
    obtain ⟨notOld,_⟩ := Finset.mem_erase.mp member
    simp only [next,Function.update_of_ne notFresh,Function.update_of_ne notOld]
  have before := Table.potential_pair keys components old fresh oldMem freshMem different
  have after := Table.potential_pair keys next old fresh oldMem freshMem different
  simp only [next,Function.update_of_ne different,Function.update_self] at after
  change _ = _ at retained
  dsimp only [next] at retained
  omega

/-- The same local budget pays for the change in the whole global state. -/
theorem Table.head_amortized {depth rotations budget : Nat} {request : α}
    {before after : PrefRouter α} (step : PrefRouter.HeadStep request depth before after)
    (distinct : before.leaves.Nodup) (components : Table α) (dormant active : Component)
    (localBound : rotations + 2*(active.potential+dormant.potential) ≤
      2*((components before.terminal).potential+(components after.terminal).potential)+budget) :
    rotations + 2*Table.potential after.leaves.toFinset
      (Function.update (Function.update components before.terminal dormant) after.terminal active) ≤
      2*components.potential before.leaves.toFinset + budget := by
  have incoming : after.terminal ∈ before.leaves.toFinset := by
    apply List.mem_toFinset.mpr
    rw [← step.leaves]
    exact after.terminal_mem
  have cancellation := Table.potential_update_pair before.leaves.toFinset components
    before.terminal after.terminal (List.mem_toFinset.mpr before.terminal_mem)
    incoming (step.endpoints_ne distinct) dormant active
  rw [step.leaves]
  omega

def State.potential {height : Nat} {reference : DepthTree 0 height} {keyWord : List α}
    (state : State reference keyWord) : Nat := state.components.potential keyWord.toFinset

end ChaCha.Paper20261030.SplayAuxiliary.Global

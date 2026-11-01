import VirtualRetainedPass
import VirtualNumericInsertion
import Splay.Interface.OperationCounts

/-! Same-matching numeric lifting. Raise only each Pass loser as far as
its original winner plus one, preserving every winner and every block.
Disjoint matching endpoints make the exact increase bill the sum of the
original pair deficits. No Insert, Delete, Split, or Create is emitted. -/

namespace Splay.Research.VirtualLoserPreparation

open Splay.Interface Splay.Interface.MatchingValid
open Splay.Research.VirtualNumericInsertion Splay.Research.VirtualRetainedPass

noncomputable def deficit {n : ℕ} (state : State n) (pair : Pairing n) : ℕ :=
  state.value pair.winner+1-state.value pair.loser

noncomputable def lifted {n : ℕ} (state : State n) : List (Pairing n) → State n
  | [] => state
  | pair::rest => lifted (setValue state pair.loser (state.value pair.loser + deficit state pair)) rest

noncomputable def prepareEvents {n : ℕ} (state : State n) : List (Pairing n) → List (Operation n)
  | [] => []
  | pair::rest => List.replicate (deficit state pair) (.valueChange pair.loser .increase) ++
      prepareEvents (setValue state pair.loser (state.value pair.loser + deficit state pair)) rest

theorem lifted_blocks {n : ℕ} (state : State n) (matching : List (Pairing n)) :
    (lifted state matching).blocks = state.blocks := by
  induction matching generalizing state with
  | nil => rfl
  | cons pair rest ih => exact ih _

theorem lifted_outside {n : ℕ} (state : State n) (matching : List (Pairing n))
    (element : Element n) (outside : element ∉ matching.map Pairing.loser) :
    (lifted state matching).value element = state.value element := by
  induction matching generalizing state with
  | nil => rfl
  | cons pair rest ih =>
      have different : element ≠ pair.loser := fun equal => outside (by simp [equal])
      have absent : element ∉ rest.map Pairing.loser := fun member => outside (List.mem_cons_of_mem _ member)
      exact (ih _ absent).trans (by simp [setValue, different])

theorem lifted_mono {n : ℕ} (state : State n) (matching : List (Pairing n)) (element : Element n) :
    state.value element ≤ (lifted state matching).value element := by
  induction matching generalizing state with
  | nil => exact le_refl _
  | cons pair rest ih =>
      apply le_trans _ (ih _)
      by_cases same : element = pair.loser
      · simp [setValue, same]
      · simp [setValue, same]

private theorem endpoints_tail {n : ℕ} {pair : Pairing n} {rest : List (Pairing n)}
    (distinct : ((pair::rest).flatMap fun pair => [pair.winner, pair.loser]).Nodup) :
    pair.winner ≠ pair.loser ∧ pair.winner ∉ rest.flatMap (fun pair => [pair.winner,pair.loser]) ∧
      pair.loser ∉ rest.flatMap (fun pair => [pair.winner,pair.loser]) ∧
      (rest.flatMap fun pair => [pair.winner,pair.loser]).Nodup := by
  obtain ⟨winnerAbsent, remaining⟩ := List.nodup_cons.mp distinct
  obtain ⟨loserAbsent, tailDistinct⟩ := List.nodup_cons.mp remaining
  exact ⟨fun equal => winnerAbsent (by simp [equal]),
    fun member => winnerAbsent (List.mem_cons_of_mem _ member), loserAbsent, tailDistinct⟩

/-- Initial winner room is the only numerical premise. No weak ordering
between current winner and loser labels is assumed. -/
theorem prepare {n : ℕ} {params : Parameters} (state : State n) (matching : List (Pairing n))
    (valid : state.Valid params)
    (distinct : (matching.flatMap fun pair => [pair.winner,pair.loser]).Nodup)
    (room : ∀ pair ∈ matching, state.value pair.winner+1 ≤ params.valueBound) :
    (lifted state matching).Valid params ∧
      (∀ pair ∈ matching, (lifted state matching).value pair.winner+1 ≤ (lifted state matching).value pair.loser) ∧
      Trace params state (prepareEvents state matching) (lifted state matching) := by
  induction matching generalizing state with
  | nil => exact ⟨valid, by simp, .nil valid⟩
  | cons pair rest ih =>
      obtain ⟨different, winnerAbsent, loserAbsent, tailDistinct⟩ := endpoints_tail distinct
      let next := setValue state pair.loser (state.value pair.loser + deficit state pair)
      have targetBound : state.value pair.loser + deficit state pair ≤ params.valueBound := by
        have := (valid.2.1 pair.loser).2
        have := room pair (by simp)
        unfold deficit
        omega
      have nextValid : next.Valid params := setValue_valid state pair.loser _ valid
        (by have := (valid.2.1 pair.loser).1; omega) targetBound
      have tailRoom : ∀ selected ∈ rest, next.value selected.winner+1 ≤ params.valueBound := by
        intro selected member
        have separate : selected.winner ≠ pair.loser := by
          intro equal
          exact loserAbsent (List.mem_flatMap.mpr ⟨selected, member, by simp [equal]⟩)
        simpa [next, setValue, separate] using room selected (List.mem_cons_of_mem _ member)
      obtain ⟨afterValid, tailStrict, tailTrace⟩ := ih next nextValid tailDistinct tailRoom
      refine ⟨afterValid, ?_, trace_append (increases_trace state pair.loser (deficit state pair) valid targetBound) tailTrace⟩
      intro selected member
      rcases List.mem_cons.mp member with equal | later
      · subst selected
        have winnerOutside : pair.winner ∉ rest.map Pairing.loser :=
          fun member => winnerAbsent ((pairingLosers_sublist rest).subset member)
        have loserOutside : pair.loser ∉ rest.map Pairing.loser :=
          fun member => loserAbsent ((pairingLosers_sublist rest).subset member)
        change (lifted next rest).value pair.winner+1 ≤ (lifted next rest).value pair.loser
        rw [lifted_outside next rest pair.winner winnerOutside, lifted_outside next rest pair.loser loserOutside]
        simp only [next, setValue, Function.update_of_ne different, Function.update_self]
        unfold deficit
        omega
      · exact tailStrict selected later

theorem prepare_increases {n : ℕ} (state : State n) (matching : List (Pairing n))
    (distinct : (matching.flatMap fun pair => [pair.winner,pair.loser]).Nodup) :
    totalIncreases (prepareEvents state matching) = (matching.map (deficit state)).sum := by
  induction matching generalizing state with
  | nil => rfl
  | cons pair rest ih =>
      obtain ⟨different, winnerAbsent, loserAbsent, tailDistinct⟩ := endpoints_tail distinct
      let next := setValue state pair.loser (state.value pair.loser + deficit state pair)
      have costs : rest.map (deficit next) = rest.map (deficit state) := by
        apply List.map_congr_left
        intro selected member
        have winnerDifferent : selected.winner ≠ pair.loser := by
          intro equal
          exact loserAbsent (List.mem_flatMap.mpr ⟨selected, member, by simp [equal]⟩)
        have loserDifferent : selected.loser ≠ pair.loser := by
          intro equal
          exact loserAbsent (List.mem_flatMap.mpr ⟨selected, member, by simp [equal]⟩)
        simp [deficit, next, setValue, winnerDifferent, loserDifferent]
      change totalIncreases (List.replicate (deficit state pair) (.valueChange pair.loser .increase) ++ prepareEvents next rest) = _
      rw [totalIncreases_append, ih next tailDistinct, costs]
      simp [totalIncreases, Operation.increaseCount]

theorem prepare_counters {n : ℕ} (state : State n) (matching : List (Pairing n)) :
    totalActivity (prepareEvents state matching) = 0 ∧ totalBlockGrowth (prepareEvents state matching) = 0 ∧
      totalInserts (prepareEvents state matching) = 0 := by
  induction matching generalizing state with
  | nil => exact ⟨rfl,rfl,rfl⟩
  | cons pair rest ih =>
      have tail := ih (setValue state pair.loser (state.value pair.loser + deficit state pair))
      simp only [prepareEvents, totalActivity_append, totalBlockGrowth_append, totalInserts_append,
        tail.1, tail.2.1, tail.2.2, Nat.add_zero]
      simp [totalActivity, totalBlockGrowth, totalInserts, Operation.activity, Operation.blockGrowth, Operation.insertCount]

noncomputable def events {n : ℕ} (state : State n) (id : ℕ) (matching : List (Pairing n)) : List (Operation n) :=
  prepareEvents state matching ++ [.pass id matching]

/-- Execute the identical original source and matching with any new bounded
labels. The only extra operations are the charged loser increases. -/
theorem realize {n : ℕ} {params : Parameters} (state : State n) (id : ℕ) (source : Block n)
    (matching : List (Pairing n)) (valid : state.Valid params) (found : state.blocks[id]? = some source)
    (structural : StructuralMatching params state id source matching)
    (room : ∀ pair ∈ matching, state.value pair.winner+1 ≤ params.valueBound) :
    Trace params state (events state id matching) (afterPass (lifted state matching) id source matching) ∧
      (afterPass (lifted state matching) id source matching).blocks = (afterPass state id source matching).blocks ∧
      totalActivity (events state id matching) = matching.length ∧
      totalBlockGrowth (events state id matching) = 0 ∧ totalInserts (events state id matching) = 0 ∧
      totalIncreases (events state id matching) = (matching.map (deficit state)).sum := by
  obtain ⟨preparedValid, strict, preparation⟩ := prepare state matching valid structural.endpoints room
  have pass := (structural.of_blocks_eq (lifted_blocks state matching)).step preparedValid
    (by simpa only [lifted_blocks] using found) strict
  have counts := prepare_counters state matching
  refine ⟨trace_append preparation (.cons pass (.nil pass.2.2)), ?_, ?_, ?_, ?_, ?_⟩
  · simp only [afterPass, lifted_blocks]
  · simp only [events, totalActivity_append, counts.1]
    simp [totalActivity, Operation.activity]
  · simp only [events, totalBlockGrowth_append, counts.2.1]
    simp [totalBlockGrowth, Operation.blockGrowth]
  · simp only [events, totalInserts_append, counts.2.2]
    simp [totalInserts, Operation.insertCount]
  · simp only [events, totalIncreases_append, prepare_increases state matching structural.endpoints]
    simp [totalIncreases, Operation.increaseCount]

end Splay.Research.VirtualLoserPreparation

#print axioms Splay.Research.VirtualLoserPreparation.realize
#print axioms Splay.Research.VirtualLoserPreparation.prepare_increases

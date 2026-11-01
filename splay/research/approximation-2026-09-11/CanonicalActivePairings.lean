import CanonicalActiveCells
import Splay.Accounting.ArticleSourcePairingGeometry

/-! Adjacency and endpoint uniqueness of the actual retained active core.
These are structural matching facts; numerical validity and density are
separate obligations. -/

namespace Splay.Research.CanonicalActive

open Splay.Rank Splay.Tree.BST Splay.Lazy.Canonical Splay.Accounting

def ActivePosition {n : ℕ} (activeKeys : Finset (Fin n)) (position : External n) : Prop :=
  ∃ key : Fin n, position = valuePos key ∧ key ∈ activeKeys

theorem valuePos_injective {n : ℕ} : Function.Injective (@valuePos n) := by
  intro first second equal
  apply Fin.ext
  have positions := congrArg Fin.val equal
  change 2*first.val+1 = 2*second.val+1 at positions
  omega

@[simp] theorem activePosition_value {n : ℕ} (activeKeys : Finset (Fin n)) (key : Fin n) :
    ActivePosition activeKeys (valuePos key) ↔ key ∈ activeKeys := by
  constructor
  · rintro ⟨other, equal, member⟩
    exact (valuePos_injective equal).symm ▸ member
  · exact fun member => ⟨key, rfl, member⟩

theorem adjacent_triple_touches_middle {α : Type*} {left middle right first second : α}
    (adjacent : Splay.Interface.Adjacent [left, middle, right] first second) :
    first = middle ∨ second = middle := by
  obtain ⟨front, back, direct | reverse⟩ := adjacent
  · have length := congrArg List.length direct
    rcases front with _ | ⟨head, _ | ⟨next, tail⟩⟩
    · simp only [List.nil_append, List.cons.injEq] at direct
      exact Or.inr direct.2.1.symm
    · simp only [List.cons_append, List.nil_append, List.cons.injEq] at direct
      exact Or.inl direct.2.1.symm
    · simp only [List.length_cons, List.length_append, List.length_nil] at length
      omega
  · have length := congrArg List.length reverse
    rcases front with _ | ⟨head, _ | ⟨next, tail⟩⟩
    · simp only [List.nil_append, List.cons.injEq] at reverse
      exact Or.inl reverse.2.1.symm
    · simp only [List.cons_append, List.nil_append, List.cons.injEq] at reverse
      exact Or.inr reverse.2.1.symm
    · simp only [List.length_cons, List.length_append, List.length_nil] at length
      omega

/-- Any endpoint pair adjacent before the first phase touches the inactive
middle position. Therefore an active winner has an inactive first loser. -/
theorem aligned_first_loser_inactive {n : ℕ} (snapshot : Snapshot n)
    (tree : Splay.Tree.BST 0 n) (key : Fin n) (rankZero : snapshot.rank (valuePos key) = 0)
    (group : ℕ) (first second : List (External n))
    (aligned : SequentialPhaseSelectionAtDoubleGroup snapshot tree (le_refl n) key.val group
      (first, second)) {winner loser : External n}
    (pair : first = [winner, loser]) (winnerActive : ActivePosition (active snapshot tree) winner) :
    ¬ ActivePosition (active snapshot tree) loser := by
  obtain ⟨extra, storedWinner, firstLoser, secondLoser, candidates, firstEq,
    secondEq, chunk, length, adjacent, rest⟩ := aligned
  have endpointEq : storedWinner = winner ∧ firstLoser = loser := by
    simpa only [List.cons.injEq, and_true] using firstEq.symm.trans pair
  rcases endpointEq with ⟨rfl, rfl⟩
  obtain ⟨left, middle, right, rfl⟩ : ∃ left middle right, candidates = [left, middle, right] := by
    rcases candidates with _ | ⟨left, _ | ⟨middle, _ | ⟨right, tail⟩⟩⟩ <;>
      simp only [List.length_cons, List.length_nil] at length
    all_goals try omega
    have empty : tail = [] := List.length_eq_zero_iff.mp (by omega)
    exact ⟨left, middle, right, by rw [empty]⟩
  obtain ⟨_, _, ⟨middleKey, middleEq, inactive⟩, _⟩ :=
    bottomUp_group_classified snapshot tree key rankZero group extra left middle right chunk
  have middleInactive : ¬ ActivePosition (active snapshot tree) middle := by
    rw [middleEq, activePosition_value]
    exact inactive
  rcases adjacent_triple_touches_middle adjacent with winnerMiddle | loserMiddle
  · exact (middleInactive (winnerMiddle ▸ winnerActive)).elim
  · simpa only [loserMiddle] using middleInactive

theorem adjacent_filter {α : Type*} (keep : α → Bool)
    {elements : List α} {first second : α}
    (adjacent : Splay.Interface.Adjacent elements first second)
    (keepFirst : keep first = true) (keepSecond : keep second = true) :
    Splay.Interface.Adjacent (elements.filter keep) first second := by
  obtain ⟨front, back, direct | reverse⟩ := adjacent
  · refine ⟨front.filter keep, back.filter keep, Or.inl ?_⟩
    simp [direct, keepFirst, keepSecond]
  · refine ⟨front.filter keep, back.filter keep, Or.inr ?_⟩
    simp [reverse, keepFirst, keepSecond]

/-- Every actual second-phase pair survives projection and any additional
paid removals that avoid its two endpoints. -/
theorem retained_second_projected_adjacent {n key : ℕ} {snapshot : Snapshot n}
    {before : Splay.Tree.BST 0 n} {groups : List ℕ}
    {elements : List (Splay.Interface.Element n)}
    {batches : ArticleRetainedPairingBatches snapshot before (le_refl n) key groups}
    (plan : ArticleSourcePairings elements batches)
    (row : ℕ × (List (External n) × List (External n))) (member : row ∈ batches.rows)
    (winner loser : External n) (pair : row.2.2 = [winner, loser])
    (keep : External n → Bool) (keepWinner : keep winner = true) (keepLoser : keep loser = true)
    (paid : List (External n))
    (fresh : ∀ removed ∈ paid, removed ≠ winner ∧ removed ≠ loser) :
    Splay.Interface.Adjacent
      ((paid.foldl List.erase (batches.firstLosers.foldl List.erase elements)).filter keep)
      winner loser := by
  obtain ⟨storedWinner, storedLoser, storedPair, adjacent⟩ :=
    plan.retainedSecondBatch_adjacent row member
  have endpointEq : storedWinner = winner ∧ storedLoser = loser := by
    simpa only [List.cons.injEq, and_true] using storedPair.symm.trans pair
  rcases endpointEq with ⟨rfl, rfl⟩
  exact adjacent_filter keep (adjacent.foldl_erase_of_fresh fresh) keepWinner keepLoser

/-- Selecting any subset of the actual second-phase rows preserves the
interface's disjoint-endpoint condition. -/
theorem retained_second_endpoints_nodup {n lower upper key : ℕ} {snapshot : Snapshot n}
    {before : Splay.Tree.BST lower upper} {upper_le_n : upper ≤ n} {groups : List ℕ}
    (batches : ArticleRetainedPairingBatches snapshot before upper_le_n key groups)
    (keep : (ℕ × (List (External n) × List (External n))) → Bool) :
    ((batches.rows.filter keep).flatMap fun row => row.2.2).Nodup := by
  have sublist : (batches.rows.filter keep).Sublist batches.rows := List.filter_sublist
  have endpoints := (sublist.map (fun row => row.2.2)).flatten
  exact endpoints.nodup batches.secondEndpoints_nodup

end Splay.Research.CanonicalActive

#print axioms Splay.Research.CanonicalActive.aligned_first_loser_inactive
#print axioms Splay.Research.CanonicalActive.retained_second_projected_adjacent
#print axioms Splay.Research.CanonicalActive.retained_second_endpoints_nodup

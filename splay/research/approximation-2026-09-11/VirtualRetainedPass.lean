import CanonicalActivePairings
import Splay.Interface.Decay

/-! Structural legality of a retained active-core Pass. Actual source-row
alignment supplies adjacency and endpoint uniqueness; strict numeric order
is the only value-dependent premise. Tied-value preparation may therefore
reuse this certificate after changing values without changing blocks. -/

namespace Splay.Research.VirtualRetainedPass

open Splay.Interface Splay.Interface.MatchingValid Splay.Research.CanonicalActive Splay.Accounting Splay.Rank

structure StructuralMatching {n : ℕ} (params : Parameters) (state : State n)
    (sourceId : ℕ) (source : Block n) (matching : List (Pairing n)) : Prop where
  shrinking : source.mode = .shrinking
  endpoints : (matching.flatMap fun pair => [pair.winner, pair.loser]).Nodup
  adjacent : ∀ pair ∈ matching, Adjacent source.elements pair.winner pair.loser
  destinations : ∀ pair ∈ matching, ∃ destination,
    state.blocks[pair.destination]? = some destination ∧ destination.mode = .growing ∧
      destination.creator = pair.winner
  fraction : source.passCount < params.exemptPasses ∨
    params.matchingNumerator*source.elements.length ≤ params.matchingDenominator*matching.length

/-- Distinct winners force distinct actual growing destinations. Thus
selecting core rows does not require a separate destination injection. -/
theorem destination_ids_nodup {n : ℕ} (state : State n) (matching : List (Pairing n))
    (endpoints : (matching.flatMap fun pair => [pair.winner, pair.loser]).Nodup)
    (destinations : ∀ pair ∈ matching, ∃ destination,
      state.blocks[pair.destination]? = some destination ∧ destination.mode = .growing ∧
        destination.creator = pair.winner) :
    (matching.map Pairing.destination).Nodup := by
  induction matching with
  | nil => simp
  | cons pair matching ih =>
      have tailDistinct : (matching.flatMap fun pair => [pair.winner, pair.loser]).Nodup :=
        (List.nodup_cons.mp (List.nodup_cons.mp endpoints).2).2
      have winnerAbsent : pair.winner ∉ matching.flatMap (fun pair => [pair.winner, pair.loser]) := by
        intro member
        exact (List.nodup_cons.mp endpoints).1 (List.mem_cons_of_mem _ member)
      rw [List.map_cons, List.nodup_cons]
      refine ⟨?_, ih tailDistinct (fun selected member => destinations selected (List.mem_cons_of_mem _ member))⟩
      intro repeated
      obtain ⟨other, member, sameId⟩ := List.mem_map.mp repeated
      obtain ⟨firstBlock, firstFound, _, firstCreator⟩ := destinations pair (by simp)
      obtain ⟨otherBlock, otherFound, _, otherCreator⟩ := destinations other (List.mem_cons_of_mem _ member)
      have sameBlock : firstBlock = otherBlock := by
        rw [sameId] at otherFound
        exact Option.some.inj (firstFound.symm.trans otherFound)
      have sameWinner : pair.winner = other.winner := by
        rw [← firstCreator, ← otherCreator, sameBlock]
      apply winnerAbsent
      exact List.mem_flatMap.mpr ⟨other, member, by simp [sameWinner]⟩

theorem StructuralMatching.of_blocks_eq {n : ℕ} {params : Parameters}
    {before after : State n} {sourceId : ℕ} {source : Block n} {matching : List (Pairing n)}
    (structural : StructuralMatching params before sourceId source matching)
    (blocks : after.blocks = before.blocks) : StructuralMatching params after sourceId source matching := by
  refine ⟨structural.shrinking, structural.endpoints, structural.adjacent, ?_, structural.fraction⟩
  intro pair member
  simpa only [blocks] using structural.destinations pair member

theorem StructuralMatching.valid {n : ℕ} {params : Parameters} {state : State n}
    {sourceId : ℕ} {source : Block n} {matching : List (Pairing n)}
    (structural : StructuralMatching params state sourceId source matching)
    (found : state.blocks[sourceId]? = some source)
    (strict : ∀ pair ∈ matching, state.value pair.winner+1 ≤ state.value pair.loser) :
    MatchingValid params state sourceId source matching := by
  refine ⟨structural.shrinking, structural.endpoints,
    destination_ids_nodup state matching structural.endpoints structural.destinations, ?_, structural.fraction⟩
  intro pair member
  obtain ⟨destination, destinationFound, growing, creator⟩ := structural.destinations pair member
  refine ⟨structural.adjacent pair member, strict pair member, ?_, destination, destinationFound, growing, creator⟩
  intro sameId
  rw [sameId, found] at destinationFound
  have sameBlock := Option.some.inj destinationFound
  have impossible : Mode.growing = Mode.shrinking := by
    rw [← growing, ← sameBlock]
    exact structural.shrinking
  cases impossible

/-- The concrete legal Pass endpoint follows without a separately assumed
post-state validity proof. -/
theorem StructuralMatching.step {n : ℕ} {params : Parameters} {state : State n}
    {sourceId : ℕ} {source : Block n} {matching : List (Pairing n)}
    (structural : StructuralMatching params state sourceId source matching)
    (valid : state.Valid params) (found : state.blocks[sourceId]? = some source)
    (strict : ∀ pair ∈ matching, state.value pair.winner+1 ≤ state.value pair.loser) :
    Step params state (.pass sourceId matching) (afterPass state sourceId source matching) :=
  afterPass_step valid found (structural.valid found strict)

private theorem aligned_flatten {n : ℕ}
    {rows : List (ℕ × (List (External n) × List (External n)))} {matching : List (Pairing n)}
    (alignment : List.Forall₂ (fun row pair => row.2.2 = [pair.winner, pair.loser]) rows matching) :
    rows.flatMap (fun row => row.2.2) = matching.flatMap (fun pair => [pair.winner, pair.loser]) := by
  induction alignment with
  | nil => rfl
  | cons related tail ih => simp only [List.flatMap_cons, related, ih]

private theorem aligned_member {n : ℕ}
    {rows : List (ℕ × (List (External n) × List (External n)))} {matching : List (Pairing n)}
    (alignment : List.Forall₂ (fun row pair => row.2.2 = [pair.winner, pair.loser]) rows matching)
    (pair : Pairing n) (member : pair ∈ matching) :
    ∃ row ∈ rows, row.2.2 = [pair.winner, pair.loser] := by
  induction alignment with
  | nil => simp at member
  | @cons row head rows matching related tail ih =>
      rcases List.mem_cons.mp member with equal | member
      · subst pair
        exact ⟨row, List.mem_cons_self, related⟩
      · obtain ⟨selected, selectedMember, selectedPair⟩ := ih member
        exact ⟨selected, List.mem_cons_of_mem _ selectedMember, selectedPair⟩

/-- Build the structural Pass certificate from a literal filtered list of
actual second-phase rows. `keep` may combine activity, a chosen contiguous
span, and further paid removals; both retained endpoints must survive. -/
theorem of_actual_rows {n key : ℕ} {params : Parameters} {snapshot : Snapshot n}
    {tree : Splay.Tree.BST 0 n} {groups : List ℕ} {elements : List (Element n)}
    {batches : ArticleRetainedPairingBatches snapshot tree (le_refl n) key groups}
    (plan : ArticleSourcePairings elements batches)
    (rowsKeep : (ℕ × (List (External n) × List (External n))) → Bool)
    (matching : List (Pairing n))
    (alignment : List.Forall₂ (fun row pair => row.2.2 = [pair.winner, pair.loser])
      (batches.rows.filter rowsKeep) matching)
    (keep : External n → Bool) (paid : List (External n))
    (state : State n) (sourceId : ℕ) (source : Block n)
    (shrinking : source.mode = .shrinking)
    (payload : source.elements =
      (paid.foldl List.erase (batches.firstLosers.foldl List.erase elements)).filter keep)
    (retained : ∀ pair ∈ matching, keep pair.winner = true ∧ keep pair.loser = true)
    (avoided : ∀ pair ∈ matching, ∀ removed ∈ paid, removed ≠ pair.winner ∧ removed ≠ pair.loser)
    (destinations : ∀ pair ∈ matching, ∃ destination,
      state.blocks[pair.destination]? = some destination ∧ destination.mode = .growing ∧
        destination.creator = pair.winner)
    (fraction : source.passCount < params.exemptPasses ∨
      params.matchingNumerator*source.elements.length ≤ params.matchingDenominator*matching.length) :
    StructuralMatching params state sourceId source matching := by
  refine ⟨shrinking, ?_, ?_, destinations, fraction⟩
  · rw [← aligned_flatten alignment]
    exact retained_second_endpoints_nodup batches rowsKeep
  · intro pair member
    obtain ⟨row, selected, rowPair⟩ := aligned_member alignment pair member
    rw [payload]
    exact retained_second_projected_adjacent plan row (List.mem_filter.mp selected).1
      pair.winner pair.loser rowPair keep (retained pair member).1 (retained pair member).2 paid
      (avoided pair member)

end Splay.Research.VirtualRetainedPass

#print axioms Splay.Research.VirtualRetainedPass.of_actual_rows
#print axioms Splay.Research.VirtualRetainedPass.StructuralMatching.step

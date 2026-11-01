import Splay.Accounting.ArticleAllPairingBatches
import Splay.Accounting.WholeSplayTranscriptPairingLinks

namespace Splay.Accounting

open Splay.Lazy Splay.Lazy.Canonical Splay.Rank Splay.Tree.BST

/-- The heap link represented by one two-element phase selection. -/
def selectionHeapLinks {n : ℕ} : List (External n) → Finset (External n × External n)
  | [winner, loser] => {(winner, loser)}
  | _ => ∅

/-- The heap links represented by a whole list of phase selections. -/
noncomputable def selectionListHeapLinks {n : ℕ} (selections : List (List (External n))) :
    Finset (External n × External n) := selections.toFinset.biUnion selectionHeapLinks

@[simp]
theorem selectionListHeapLinks_nil {n : ℕ} : selectionListHeapLinks ([] : List (List (External n))) = ∅ := by
  simp [selectionListHeapLinks]

@[simp]
theorem selectionListHeapLinks_cons {n : ℕ} (first : List (External n)) (rest : List (List (External n))) :
    selectionListHeapLinks (first :: rest) = selectionHeapLinks first ∪ selectionListHeapLinks rest := by
  simp [selectionListHeapLinks]

/-- Both indexed endpoint phases enumerate precisely the step's link set. -/
theorem ZigZigBothPairingEndpointsAt.stepPairingLinks_eq {n depth key lower upper : ℕ}
    {snapshot : Snapshot n} {before after : BST lower upper} {winner firstLoser secondLoser : External n}
    (both : ZigZigBothPairingEndpointsAt snapshot (depth := depth) (key := key) before after winner firstLoser secondLoser) :
    stepPairingLinks snapshot depth key before after = {(winner, firstLoser), (winner, secondLoser)} := by
  induction both with
  | zigZigLeft a b c d bound =>
      rw [stepPairingLinks_zigZigLeft _ _ _ _ _ bound, edgesAtNode_heapLinks_eq_pairings]
      rfl
  | zigZigRight a b c d bound secondBound =>
      rw [stepPairingLinks_zigZigRight _ _ _ _ _ bound secondBound, edgesAtNode_heapLinks_eq_pairings]
      rfl
  | leftContext inner right ih =>
      rw [stepPairingLinks_leftContext _ _ _ right inner.first.key_bounds.2]
      exact ih
  | @rightContext depth key lower root upper left before after winner firstLoser secondLoser inner ih =>
      rw [stepPairingLinks_rightContext (key := key) _ left before after (by have := inner.first.key_bounds; omega)]
      exact ih

/-- The actual joint phase transcript enumerates every chronological phase
link, including all rotations inside arbitrary unchanged search context. -/
theorem SplayExecutionTranscript.BothPhaseSelections.heapLinks_eq {n key lower upper : ℕ}
    {snapshot : Snapshot n} {before after : BST lower upper} {execution : SplayExecution key before after}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    {transcript : SplayExecutionTranscript key execution kinds zig zigZig zigZag}
    {firstSelections secondSelections : List (List (External n))}
    (joint : SplayExecutionTranscript.BothPhaseSelections snapshot key transcript firstSelections secondSelections) :
    transcriptPairingLinks snapshot transcript =
      selectionListHeapLinks firstSelections ∪ selectionListHeapLinks secondSelections := by
  induction joint with
  | done root => rw [transcriptPairingLinks_done _ root]; simp
  | zig head tail transcript rest ih => rw [transcriptPairingLinks_zig _ head tail transcript]; exact ih
  | zigZag head orientation tail transcript rest ih =>
      rw [transcriptPairingLinks_zigZag _ head orientation tail transcript]
      exact ih
  | zigZig head orientation tail transcript endpoints rest ih =>
      rw [transcriptPairingLinks_zigZig _ head orientation tail transcript, endpoints.stepPairingLinks_eq, ih]
      simp only [selectionListHeapLinks_cons, selectionHeapLinks]
      simp only [Finset.insert_eq, Finset.union_assoc, Finset.union_left_comm]

/-- The two links of one retained article row, independent of phase order. -/
def articleRowHeapLinks {n : ℕ} (row : ℕ × (List (External n) × List (External n))) :
    Finset (External n × External n) := selectionHeapLinks row.2.1 ∪ selectionHeapLinks row.2.2

/-- A triple with a strict rank-minimum winner determines its two directed
heap links uniquely; either order for its two loser phases is allowed. -/
theorem triple_pairingLinks_unique {n : ℕ} (snapshot : Snapshot n)
    {winner first second otherWinner otherFirst otherSecond : External n}
    (same : ([winner, first, second] : List (External n)).Perm [otherWinner, otherFirst, otherSecond])
    (firstRank : snapshot.rank winner < snapshot.rank first)
    (secondRank : snapshot.rank winner < snapshot.rank second)
    (otherFirstRank : snapshot.rank otherWinner < snapshot.rank otherFirst)
    (otherSecondRank : snapshot.rank otherWinner < snapshot.rank otherSecond) :
    ({(winner, first), (winner, second)} : Finset (External n × External n)) =
      {(otherWinner, otherFirst), (otherWinner, otherSecond)} := by
  have winnerEq : winner = otherWinner := by
    by_contra different
    have firstMember := same.mem_iff.mp (show winner ∈ [winner, first, second] by simp)
    have secondMember := same.mem_iff.mpr (show otherWinner ∈ [otherWinner, otherFirst, otherSecond] by simp)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at firstMember secondMember
    have greater : snapshot.rank winner < snapshot.rank otherWinner := by
      rcases secondMember with equal | equal | equal
      · exact (different equal.symm).elim
      · simpa only [equal] using firstRank
      · simpa only [equal] using secondRank
    have lesser : snapshot.rank otherWinner < snapshot.rank winner := by
      rcases firstMember with equal | equal | equal
      · exact (different equal).elim
      · simpa only [equal] using otherFirstRank
      · simpa only [equal] using otherSecondRank
    omega
  subst otherWinner
  have losers : ({first, second} : Finset (External n)) = {otherFirst, otherSecond} :=
    by
      ext element
      simpa using same.cons_inv.mem_iff (a := element)
  have mapped := congrArg (fun set : Finset (External n) => set.image (fun loser => (winner, loser))) losers
  simpa only [Finset.image_insert, Finset.image_singleton] using mapped

/-- Two valid selections aligned with the same original four-child group
have identical heap links, even when their middle-winner phase order differs. -/
theorem SequentialPhaseSelectionAtDoubleGroup.heapLinks_unique {n lower upper key group : ℕ}
    {snapshot : Snapshot n} {before : BST lower upper} {bound : upper ≤ n}
    {first second : List (External n) × List (External n)}
    (firstAligned : SequentialPhaseSelectionAtDoubleGroup snapshot before bound key group first)
    (secondAligned : SequentialPhaseSelectionAtDoubleGroup snapshot before bound key group second) :
    selectionHeapLinks first.1 ∪ selectionHeapLinks first.2 =
      selectionHeapLinks second.1 ∪ selectionHeapLinks second.2 := by
  obtain ⟨extra, winner, firstLoser, secondLoser, candidates, firstEq, secondEq,
    chunkEq, _, _, _, _, perm, firstRank, secondRank⟩ := firstAligned
  obtain ⟨otherExtra, otherWinner, otherFirst, otherSecond, otherCandidates, otherFirstEq, otherSecondEq,
    otherChunkEq, _, _, _, _, otherPerm, otherFirstRank, otherSecondRank⟩ := secondAligned
  have candidatesEq := (List.cons.inj (chunkEq.symm.trans otherChunkEq)).2
  rw [candidatesEq] at perm
  have same := perm.symm.trans otherPerm
  rw [firstEq, secondEq, otherFirstEq, otherSecondEq]
  simpa only [selectionHeapLinks, Finset.singleton_union] using
    triple_pairingLinks_unique snapshot same firstRank secondRank otherFirstRank otherSecondRank

end Splay.Accounting

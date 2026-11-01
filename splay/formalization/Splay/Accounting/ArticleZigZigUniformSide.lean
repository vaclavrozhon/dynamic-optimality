import Splay.Accounting.ArticlePairingRowPartition

namespace Splay.Accounting

open Splay.Lazy Splay.Lazy.Canonical Splay.Rank Splay.Tree.BST

/-- A genuine zig-zig consumes four light children on the same side. -/
theorem HitSideSchedule.zigZig_chunk_uniform {kinds : List SplayStepKind} {sides : List Side}
    (schedule : HitSideSchedule kinds sides) {group : ℕ}
    (member : group ∈ zigZigDoubleGroupIndices kinds 0) :
    ∃ side : Side, ((duplicateHitSides sides).drop (4 * group)).take 4 = [side, side, side, side] := by
  induction schedule generalizing group with
  | done => simp [zigZigDoubleGroupIndices] at member
  | zig => simp [zigZigDoubleGroupIndices] at member
  | @zigZig kinds sides side tail ih =>
    simp only [zigZigDoubleGroupIndices, List.mem_cons] at member
    rcases member with rfl | member
    · exact ⟨side, by simp [duplicateHitSides]⟩
    · rw [zigZigDoubleGroupIndices_succ] at member
      obtain ⟨previous, previousMember, rfl⟩ := List.mem_map.mp member
      obtain ⟨nextSide, uniform⟩ := ih previousMember
      exact ⟨nextSide, by simpa [duplicateHitSides, Nat.mul_succ] using uniform⟩
  | @zigZag kinds sides first second opposite tail ih =>
    change group ∈ zigZigDoubleGroupIndices kinds 1 at member
    rw [zigZigDoubleGroupIndices_succ] at member
    obtain ⟨previous, previousMember, rfl⟩ := List.mem_map.mp member
    obtain ⟨nextSide, uniform⟩ := ih previousMember
    exact ⟨nextSide, by simpa [duplicateHitSides, Nat.mul_succ] using uniform⟩

/-- The side uniformity belongs to each literal retained row's original
four-child group, independently of its eventual internal/boundary class. -/
theorem ArticleRetainedPairingBatches.row_chunk_uniform {n : ℕ} {snapshot : Snapshot n}
    {before after : BST 0 n} {key : Fin n} {kinds : List SplayStepKind}
    {execution : SplayExecution key.val before after} {zig zigZig zigZag : ℕ}
    (batches : ArticleRetainedPairingBatches snapshot before (Nat.le_refl n) key.val (zigZigDoubleGroupIndices kinds 0))
    (transcript : SplayExecutionTranscript key.val execution kinds zig zigZig zigZag)
    (rankZero : snapshot.rank (valuePos key) = 0)
    {row : ℕ × (List (External n) × List (External n))} (member : row ∈ batches.rows) :
    ∃ side : Side, ∀ element ∈ ((rootHeavyPathChildrenBottomUp snapshot before (Nat.le_refl n) key.val 0).drop
      (4 * row.1)).take 4, canonicalSide snapshot before element = side := by
  have groupMember := batches.groups_perm.mem_iff.mp (List.mem_map.mpr ⟨row, member, rfl⟩)
  obtain ⟨side, uniform⟩ := transcript.hitSideSchedule.zigZig_chunk_uniform groupMember
  have sideMap : (((rootHeavyPathChildrenBottomUp snapshot before (Nat.le_refl n) key.val 0).drop
      (4 * row.1)).take 4).map (canonicalSide snapshot before) = [side, side, side, side] := by
    rw [List.map_take, List.map_drop, map_canonicalSide_rootHeavyPathChildrenBottomUp snapshot before key.isLt rankZero]
    exact uniform
  refine ⟨side, ?_⟩
  intro element inside
  have sideMember := (List.mem_map (f := canonicalSide snapshot before)).mpr ⟨element, inside, rfl⟩
  rw [sideMap] at sideMember
  simpa using sideMember

end Splay.Accounting

import Splay.Accounting.ArticleChronologicalExecution
import Splay.Accounting.SplayDeterminism

namespace Splay.Accounting.ArticleMacroHistory

open Splay.Tree.BST

variable {n : ℕ} {params : Interface.Parameters} {first last : ArticleCheckpoint n}

/-- Forget comparison operations while retaining every actual splay execution. -/
noncomputable def toSplaySequence {first last : ArticleCheckpoint n} (history : ArticleMacroHistory params first last) :
    SplaySequence history.requests first.splay last.splay :=
  match history with
  | .done checkpoint _ => .done checkpoint.splay
  | .next (.rotation _ _ _) tail => tail.toSplaySequence
  | .next (.request _ _ execution _ _) tail => .next execution tail.toSplaySequence

/-- The transcript extracted from the history is exactly its concatenated
local transcript, even when comparison operations separate requests. -/
theorem exists_transcript (history : ArticleMacroHistory params first last) :
    ∃ zig zigZig zigZag, SplaySequenceTranscript history.toSplaySequence history.kinds zig zigZig zigZag := by
  induction history with
  | done checkpoint represented => exact ⟨0, 0, 0, .done checkpoint.splay⟩
  | next head tail ih =>
      obtain ⟨zig, zigZig, zigZag, transcript⟩ := ih
      cases head with
      | rotation represented rotation execution => exact ⟨zig, zigZig, zigZag, transcript⟩
      | request represented root execution witness request =>
          exact ⟨witness.zig + zig, witness.zigZig + zigZig, witness.zigZag + zigZag,
            .next execution tail.toSplaySequence witness.transcript transcript⟩

theorem kinds_eq_concrete (history : ArticleMacroHistory params first last) :
    history.kinds = (concreteSplayTranscript first.splay history.requests).kinds := by
  obtain ⟨zig, zigZig, zigZag, transcript⟩ := history.exists_transcript
  exact transcript.eq_concrete.1

theorem concrete_zigZigs_le_activity_add_inserts (history : ArticleMacroHistory params first last) :
    2 * (concreteSplayTranscript first.splay history.requests).zigZig ≤
      Interface.totalActivity (Lazy.eraseOperations history.events) +
        Interface.totalInserts (Lazy.eraseOperations history.events) := by
  have bound := history.zigZigs_le_activity_add_inserts
  rw [history.kinds_eq_concrete, (concreteSplayTranscript first.splay history.requests).transcript.count_zigZig] at bound
  exact bound

end Splay.Accounting.ArticleMacroHistory

namespace Splay.Accounting.ArticleChronologicalExecution

open Splay.Tree.BST

theorem concrete_zigZigs_le_activity_add_boundary
    {n : ℕ} {params : Interface.Parameters} {initial : ArticleCheckpoint n}
    {comparison splay : BST 0 n} {accesses : List (Fin n)} {rotations requestBudget rotationBudget : ℕ}
    (execution : ArticleChronologicalExecution params initial comparison splay accesses rotations requestBudget rotationBudget) :
    2 * (concreteSplayTranscript initial.splay accesses).zigZig ≤
      Interface.totalActivity (Lazy.eraseOperations execution.history.events) + rotations +
        2 * execution.history.boundaryCount := by
  have zig := execution.history.concrete_zigZigs_le_activity_add_inserts
  rw [execution.requests_eq] at zig
  have insert := execution.history.inserts
  rw [execution.rotations_eq] at insert
  omega

end Splay.Accounting.ArticleChronologicalExecution

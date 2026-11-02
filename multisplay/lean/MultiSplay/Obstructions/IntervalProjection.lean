import MultiSplay.SplayDeterminism
import DynamicOptimality.SearchRotationProjection

/-!
# Ordinary splay does not commute with interval restriction

This four-key witness is the appendix example in
`research-2026-11-01/MixedArityPartialAccessLemma.txt`. Both executions
are literal bottom-up splay transcripts. Restricting the actual output
and splaying the restricted input give distinct three-key endpoints.
This concerns endpoint geometry, not a lower bound on competitiveness.
-/

namespace MultiSplay.Obstructions.IntervalProjection

open DynamicOptimality (RawTree)
open Auxiliary
open ChaCha.MTR.Tree
open DynamicOptimality.SearchRotation.Prefix

def input : RawTree Nat := .node .empty 0 (.node .empty 1 (.node (.node .empty 2 .empty) 3 .empty))

def output : RawTree Nat := .node (.node .empty 0 (.node .empty 1 .empty)) 2 (.node .empty 3 .empty)

def restrictedOutput : RawTree Nat := .node (.node (.node .empty 0 .empty) 1 .empty) 2 .empty

theorem input_word : input.inorder = [0,1,2,3] := rfl

theorem input_ordered : input.Ordered := by
  change ([0,1,2,3] : List Nat).Pairwise (· < ·)
  decide

theorem actual_splay : Splay 2 input output 3 := by
  exact .next (.double (.rightContext .empty 0 (.rightLeft .empty .empty .empty .empty 1 3)))
    (.next (.zigRight .empty (.node .empty 1 .empty) (.node .empty 3 .empty) 0) (.done _ _))

theorem restricted_splay : Splay 2 (prune 3 input) restrictedOutput 2 := by
  exact .next (.double (.rightRight .empty .empty .empty .empty 0 1)) (.done _ _)

theorem endpoints_differ : prune 3 output ≠ restrictedOutput := by decide

/-- No genuine ordinary splay of the restricted initial tree reaches the
restriction of the actual four-key output, regardless of its stated cost. -/
theorem restriction_not_splay (rotations : Nat) : ¬ Splay 2 (prune 3 input) (prune 3 output) rotations := by
  intro execution
  have unique : (prune 3 input).inorder.Nodup := by decide
  have same := restricted_splay.deterministic execution unique
  exact endpoints_differ same.1.symm

/-- The comparison is between actual ordered BSTs on the same three keys. -/
theorem exact_interval_counterexample :
    input.Ordered ∧ Splay 2 input output 3 ∧
    (prune 3 input).inorder = [0,1,2] ∧ Splay 2 (prune 3 input) restrictedOutput 2 ∧
    prune 3 output ≠ restrictedOutput :=
  ⟨input_ordered,actual_splay,rfl,restricted_splay,endpoints_differ⟩

end MultiSplay.Obstructions.IntervalProjection

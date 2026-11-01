import Splay.Lazy.CanonicalInitializationTrace
import Splay.Lazy.SplayTrace

namespace Splay.Tree.BST

/--
A dependent sequence of complete splay accesses.

Each constructor carries the genuine `SplayExecution` serving the head
request, and the intermediate tree is shared definitionally with the tail.
Keeping this object in `Type` lets later definitions compute the exact list of
pre-access depths.
-/
inductive SplaySequence {n : ℕ} :
    List (Fin n) → BST 0 n → BST 0 n → Type
  | done (tree : BST 0 n) :
      SplaySequence [] tree tree
  | next {access : Fin n} {accesses : List (Fin n)}
      {before middle after : BST 0 n}
      (head : SplayExecution access.val before middle)
      (tail : SplaySequence accesses middle after) :
      SplaySequence (access :: accesses) before after

namespace SplaySequence

/-- The search depth immediately before each access in the sequence. -/
def preAccessDepths {n : ℕ} {accesses : List (Fin n)}
    {before after : BST 0 n} :
    SplaySequence accesses before after → List ℕ
  | .done _ => []
  | .next (access := access) (before := before) head tail =>
      before.depth access.val :: preAccessDepths tail

/-- Total number of ordinary rotations performed by the sequence. -/
def rotationCount {n : ℕ} {accesses : List (Fin n)}
    {before after : BST 0 n}
    (sequence : SplaySequence accesses before after) : ℕ :=
  sequence.preAccessDepths.sum

@[simp]
theorem preAccessDepths_done {n : ℕ} (tree : BST 0 n) :
    (SplaySequence.done tree).preAccessDepths = [] :=
  rfl

@[simp]
theorem preAccessDepths_next {n : ℕ}
    {access : Fin n} {accesses : List (Fin n)}
    {before middle after : BST 0 n}
    (head : SplayExecution access.val before middle)
    (tail : SplaySequence accesses middle after) :
    (SplaySequence.next head tail).preAccessDepths =
      before.depth access.val :: tail.preAccessDepths :=
  rfl

@[simp]
theorem rotationCount_done {n : ℕ} (tree : BST 0 n) :
    (SplaySequence.done tree).rotationCount = 0 :=
  rfl

@[simp]
theorem rotationCount_next {n : ℕ}
    {access : Fin n} {accesses : List (Fin n)}
    {before middle after : BST 0 n}
    (head : SplayExecution access.val before middle)
    (tail : SplaySequence accesses middle after) :
    (SplaySequence.next head tail).rotationCount =
      before.depth access.val + tail.rotationCount := by
  simp [rotationCount]

/-- There is one recorded pre-access depth for every served request. -/
@[simp]
theorem preAccessDepths_length {n : ℕ}
    {accesses : List (Fin n)}
    {before after : BST 0 n}
    (sequence : SplaySequence accesses before after) :
    sequence.preAccessDepths.length = accesses.length := by
  induction sequence with
  | done =>
      rfl
  | next head tail ih =>
      simpa only [preAccessDepths_next, List.length_cons,
        Nat.succ_eq_add_one] using congrArg Nat.succ ih

/-- Every complete access sequence preserves the exact number of keys. -/
theorem size_eq {n : ℕ} {accesses : List (Fin n)}
    {before after : BST 0 n}
    (sequence : SplaySequence accesses before after) :
    before.size = after.size := by
  induction sequence with
  | done =>
      rfl
  | next head tail ih =>
      exact head.size_eq.trans ih

/-- In particular, the final indexed tree still contains exactly `n` keys. -/
@[simp]
theorem final_size {n : ℕ} {accesses : List (Fin n)}
    {before after : BST 0 n}
    (sequence : SplaySequence accesses before after) :
    after.size = n := by
  rw [← sequence.size_eq]
  exact size_eq_upper before

/--
Flattening all head executions gives one ordinary-rotation execution whose
length is exactly the sum of the successive pre-access depths.
-/
theorem toRotationExecution {n : ℕ}
    {accesses : List (Fin n)}
    {before after : BST 0 n}
    (sequence : SplaySequence accesses before after) :
    RotationExecution sequence.rotationCount before after := by
  induction sequence with
  | done tree =>
      exact .refl
  | @next access accesses before middle after head tail ih =>
      rw [rotationCount_next]
      exact head.toRotationExecution.append ih

/--
Every finite request list has a constructive sequence of complete standard
splay executions from any initial indexed tree.
-/
theorem exists_sequence {n : ℕ} (initial : BST 0 n)
    (accesses : List (Fin n)) :
    ∃ final : BST 0 n,
      Nonempty (SplaySequence accesses initial final) := by
  induction accesses generalizing initial with
  | nil =>
      exact ⟨initial, ⟨.done initial⟩⟩
  | cons access accesses ih =>
      obtain ⟨middle, head⟩ :=
        SplayExecution.exists_splay initial
          (Nat.zero_le access.val) access.isLt
      obtain ⟨final, ⟨tail⟩⟩ := ih middle
      exact ⟨final, ⟨.next head tail⟩⟩

end SplaySequence

end Splay.Tree.BST

namespace Splay.Tree.BST.SplaySequence

open Splay.Lazy
open Splay.Rank

/--
A fixed-snapshot realizer for one ordinary splay rotation lifts to a single
represented transition for the entire access sequence.
-/
theorem existsRepresentedTransition
    {params : Interface.Parameters}
    {n : ℕ} {snapshot : Snapshot n}
    (realizer : SplayRotationTraceRealizer params snapshot)
    {accesses : List (Fin n)}
    {beforeTree afterTree : BST 0 n}
    (sequence : SplaySequence accesses beforeTree afterTree)
    {initial : State n}
    (initialRepresents :
      initial.Represents params snapshot beforeTree) :
    Nonempty
      (RepresentedTransition params
        snapshot beforeTree snapshot afterTree initial) :=
  sequence.toRotationExecution.existsRepresentedSplayTransition
    realizer initialRepresents

/--
The same lift, started from the concrete canonical initialization constructed
from primitive events.  No caller-supplied initialization witness is needed.
-/
noncomputable def initializedTransition
    {params : Interface.Parameters}
    {n : ℕ} {snapshot : Snapshot n}
    (realizer : SplayRotationTraceRealizer params snapshot)
    {accesses : List (Fin n)}
    {beforeTree afterTree : BST 0 n}
    (sequence : SplaySequence accesses beforeTree afterTree)
    (growingLimit : 2 ≤ params.growingLimit)
    (valueBound :
      Analysis.contractedGap snapshot.maxRank ≤ params.valueBound) :
    InitializedTransition params
      snapshot beforeTree snapshot afterTree := by
  let initialization :=
    Canonical.canonicalInitialization snapshot beforeTree params
      growingLimit valueBound
  let transition :=
    Classical.choice
      (sequence.existsRepresentedTransition realizer
        initialization.final_represents)
  exact
    { initialization := initialization
      transition := transition }

/-- Existence form of `initializedTransition` for proposition-oriented APIs. -/
theorem existsInitializedTransition
    {params : Interface.Parameters}
    {n : ℕ} {snapshot : Snapshot n}
    (realizer : SplayRotationTraceRealizer params snapshot)
    {accesses : List (Fin n)}
    {beforeTree afterTree : BST 0 n}
    (sequence : SplaySequence accesses beforeTree afterTree)
    (growingLimit : 2 ≤ params.growingLimit)
    (valueBound :
      Analysis.contractedGap snapshot.maxRank ≤ params.valueBound) :
    Nonempty
      (InitializedTransition params
        snapshot beforeTree snapshot afterTree) :=
  ⟨sequence.initializedTransition realizer
    growingLimit valueBound⟩

end Splay.Tree.BST.SplaySequence

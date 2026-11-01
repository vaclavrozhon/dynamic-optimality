import MultiSplay.SharedSplayHistory
import MultiSplay.InterfaceFrameComposition
import MultiSplay.RichSplitFramed

/-!
# Constructive component operations in a shared history

`Certified` bundles the actual lazy representation with the two temporal
invariants used by the splay analysis. Requests and comparison rotations build
their own article witnesses and preserve these invariants. Common boundaries
use their actual strict traces and preserve the same historical records.
-/

namespace MultiSplay.SharedSplay

open Splay.Accounting
open Splay.Rank (Snapshot)
open Splay.Tree.BST

variable {n m l r : Nat} {params : Splay.Interface.Parameters}

structure Certified (params : Splay.Interface.Parameters) (checkpoint : ArticleCheckpoint n) : Prop where
  represented : checkpoint.state.Represents params (Snapshot.ofTree checkpoint.comparison).withTruePriority checkpoint.splay
  growingZero : Splay.Interface.GrowingPassCountZero checkpoint.state.toInterface
  unbroken : PassedBlocksUnbroken (Snapshot.ofTree checkpoint.comparison).withTruePriority checkpoint.splay checkpoint.state

theorem Certified.after {before after : ArticleCheckpoint n} (valid : Certified params before)
    (step : ArticleMacro params before after) : Certified params after :=
  ⟨step.final_represents, step.trace.growingPassCountZero valid.growingZero,
    step.preservesUnbroken valid.growingZero valid.unbroken⟩

/-- A real complete splay supplies both the new certified local state and the
segment in the same global interface history. -/
theorem request {comparison before after : Splay.Tree.BST 0 n} {key : Fin n} {state : Splay.Lazy.State n}
    (valid : Certified params ⟨comparison, before, state⟩)
    (root : comparison.HasRoot key.val) (execution : SplayExecution key.val before after)
    (valueBound : Splay.Analysis.contractedGap (2 * (Snapshot.ofTree comparison).maxRank + 1) ≤ params.valueBound)
    (whole : Splay.Interface.State m) (framed : InterfaceFramedTrace.Framed params state.toInterface whole) :
    ∃ final : Splay.Lazy.State n, ∃ globalAfter : Splay.Interface.State m,
      Certified params ⟨comparison, after, final⟩ ∧
      Nonempty (InterfaceFramedTrace.Framed params final.toInterface globalAfter) ∧
      ∃ step : ArticleMacro params ⟨comparison, before, state⟩ ⟨comparison, after, final⟩,
        step.requests = [key] ∧ ∃ segment : Segment params whole globalAfter,
          segment.boundary = step.boundaryCount ∧ segment.rotations = 0 ∧
          segment.births = step.birthBudget ∧ segment.maintenanceCost = 0 ∧
          segment.zigZigs = step.kinds.count .zigZig := by
  obtain ⟨final, step, requests, ⟨run⟩⟩ := FramedSplay.exists_request valid.represented root execution valueBound whole framed
  have rotationZero : step.rotationCount = 0 := by
    cases step with
    | rotation rep rotation realizer => simp [ArticleMacro.requests] at requests
    | request rep root execution transcript realizer => rfl
  exact ⟨final, run.final, valid.after step, ⟨run.framed⟩, step, requests,
    .article step valid.unbroken framed run, rfl, rotationZero, rfl, rfl, rfl⟩

theorem rotation {before after splay : Splay.Tree.BST 0 n} {depth : Nat} {state : Splay.Lazy.State n}
    (valid : Certified params ⟨before, splay, state⟩) (turn : RotationAt depth before after)
    (whole : Splay.Interface.State m) (framed : InterfaceFramedTrace.Framed params state.toInterface whole) :
    ∃ final : Splay.Lazy.State n, ∃ globalAfter : Splay.Interface.State m,
      Certified params ⟨after, splay, final⟩ ∧
      Nonempty (InterfaceFramedTrace.Framed params final.toInterface globalAfter) ∧
      ∃ step : ArticleMacro params ⟨before, splay, state⟩ ⟨after, splay, final⟩,
        step.rotationCount = 1 ∧ ∃ segment : Segment params whole globalAfter,
          segment.rotations = 1 ∧ segment.births = step.birthBudget ∧ segment.maintenanceCost = 0 := by
  obtain ⟨final, step, rotations, ⟨run⟩⟩ := FramedSplay.exists_rotation valid.represented turn whole framed
  exact ⟨final, run.final, valid.after step, ⟨run.framed⟩, step, rotations,
    .article step valid.unbroken framed run, rotations, rfl, rfl⟩

/-- Both split outputs continue inside the original global state, even when
the parent was itself a component of a larger forest. -/
theorem split (left : Splay.Tree.BST 0 l) (right : Splay.Tree.BST 0 r)
    (sl : Splay.Tree.BST 0 l) (sr : Splay.Tree.BST 0 r) (source : Splay.Lazy.State (0+l+1+r))
    (valid : Certified params ⟨JoinRanks.tree left right, JoinRanks.tree sl sr, source⟩)
    (whole : Splay.Interface.State m) (framed : InterfaceFramedTrace.Framed params source.toInterface whole) :
    ∃ a : Splay.Lazy.State l, ∃ b : Splay.Lazy.State r, ∃ final : Splay.Interface.State m,
      Certified params ⟨left, sl, a⟩ ∧ Certified params ⟨right, sr, b⟩ ∧
      Nonempty (InterfaceFramedTrace.Framed params a.toInterface final) ∧
      Nonempty (InterfaceFramedTrace.Framed params b.toInterface final) ∧
      ∃ segment : Segment params whole final, segment.maintenanceCost ≤ 8 ∧
        segment.rotations = 0 ∧ segment.boundary = 0 ∧ segment.births = 0 ∧
        Splay.Interface.totalInserts segment.operations = 0 ∧
        Splay.Interface.totalIncreases segment.operations = 0 ∧ Splay.Interface.totalActivity segment.operations = 0 := by
  obtain ⟨boundary, execution, aRep, bRep, ⟨aFrame⟩, ⟨bFrame⟩, length, inserts, increases, activity⟩ :=
    RichSplit.exists_framed_split left right sl sr source valid.represented
  obtain ⟨word, final, globalRun, ⟨next, _, _⟩, wordLength, wordActivity, wordInserts, wordIncreases, _⟩ := framed.trace execution
  refine ⟨_, _, final, ?_, ?_, ⟨aFrame.comp next⟩, ⟨bFrame.comp next⟩,
    .maintenance globalRun, ?_, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · exact ⟨aRep, RichRestriction.growing_zero source _ _ valid.growingZero,
      RichSplit.left_unbroken left right sl sr source valid.represented valid.unbroken⟩
  · exact ⟨bRep, RichRestriction.growing_zero source _ _ valid.growingZero,
      RichSplit.right_unbroken left right sl sr source valid.represented valid.unbroken⟩
  · change word.length ≤ 8
    omega
  · exact wordInserts.trans inserts
  · exact wordIncreases.trans increases
  · exact wordActivity.trans activity

/-- The caller identifies the two existing children jointly in the current
forest; the common root and all eight strict join operations are constructed. -/
theorem join (left : Splay.Tree.BST 0 l) (right : Splay.Tree.BST 0 r)
    (sl : Splay.Tree.BST 0 l) (sr : Splay.Tree.BST 0 r) (a : Splay.Lazy.State l) (b : Splay.Lazy.State r)
    (aValid : Certified params ⟨left, sl, a⟩) (bValid : Certified params ⟨right, sr, b⟩)
    (growingLimit : 2 ≤ params.growingLimit) (valueCap : 3 ≤ params.valueBound)
    (whole : Splay.Interface.State m)
    (framed : InterfaceFramedTrace.Framed params (InterfaceCommonJoin.initial a.toInterface b.toInterface) whole) :
    ∃ source : Splay.Lazy.State (0+l+1+r), ∃ final : Splay.Interface.State m,
      Certified params ⟨JoinRanks.tree left right, JoinRanks.tree sl sr, source⟩ ∧
      Nonempty (InterfaceFramedTrace.Framed params source.toInterface final) ∧
      ∃ segment : Segment params whole final, segment.maintenanceCost ≤ 8 ∧
        segment.rotations = 0 ∧ segment.boundary = 0 ∧ segment.births = 0 ∧
        Splay.Interface.totalInserts segment.operations = 2 ∧
        Splay.Interface.totalIncreases segment.operations = 4 ∧ Splay.Interface.totalActivity segment.operations = 0 := by
  have execution := RichJoin.interface_trace left right sl sr a b aValid.represented bValid.represented growingLimit valueCap
  obtain ⟨word, final, globalRun, ⟨next, _, _⟩, wordLength, wordActivity, wordInserts, wordIncreases, _⟩ := framed.trace execution
  refine ⟨RichJoin.state left right sl sr a b, final, ?_, ⟨next⟩,
    .maintenance globalRun, ?_, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · exact ⟨RichJoin.represents left right sl sr a b aValid.represented bValid.represented growingLimit valueCap,
      RichJoin.growing_zero left right sl sr a b aValid.growingZero bValid.growingZero,
      RichJoin.unbroken left right sl sr a b aValid.represented bValid.represented aValid.unbroken bValid.unbroken⟩
  · change word.length ≤ 8
    rw [wordLength]
    rfl
  · exact wordInserts.trans (InterfaceCommonJoin.inserts _ _ _ _)
  · exact wordIncreases.trans (InterfaceCommonJoin.increases _ _ _ _)
  · exact wordActivity.trans (InterfaceCommonJoin.activity _ _ _ _)

end MultiSplay.SharedSplay

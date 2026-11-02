import ChaCha.Paper20261030.GraftedPointer
import ChaCha.Paper20261030.ChargedSplit

/-!
# Charged auxiliary operations with untouched payload attachments

Every empty auxiliary slot may contain an arbitrary actual subtree.
Record reads, cache writes, payload-field writes, moves, and rotations
lift to these attachments without increasing their cost. In particular,
split and join do not charge for or traverse the payload interiors.
-/

namespace ChaCha.Paper20261030.Auxiliary.Metadata

open ChaCha.MTR
open Std Std.DTreeMap.Internal Std.DTreeMap.Internal.Impl

variable {α : Type*} {β : α → Type*}

theorem Step.extend {c d : Cursor α β} (h : Step c d)
    (outside : List (Pointer.Frame (NodeRecord α β))) :
    Step (PointerGraft.extend c outside) (PointerGraft.extend d outside) := by
  cases h with
  | nav move => exact .nav (PointerGraft.step_extend move outside)
  | write => exact .write _ _ _ _ _ _
  | writeValue => exact .writeValue _ _ _ _ _ _ _

theorem Trace.extend {c d : Cursor α β} {reads : List (NodeRecord α β)} {cost : Nat}
    (h : Trace c reads d cost) (outside : List (Pointer.Frame (NodeRecord α β))) :
    Trace (PointerGraft.extend c outside) reads (PointerGraft.extend d outside) cost := by
  induction h with
  | nil => exact .nil _
  | step move rest ih => exact .step (move.extend outside) ih
  | read atRecord rest ih => exact .read atRecord ih

theorem Step.graft {c d : Cursor α β} (h : Step c d)
    (gaps : Nat → MTR.Tree (NodeRecord α β)) (base : Nat) :
    Step (PointerGraft.cursor gaps base c) (PointerGraft.cursor gaps base d) := by
  cases h with
  | nav move => exact .nav (PointerGraft.step move gaps base)
  | write l r old fresh entry ancestors =>
    exact .write _ _ _ _ _ _
  | writeValue l r size key old fresh ancestors =>
    exact .writeValue _ _ _ _ _ _ _

theorem Trace.graft {c d : Cursor α β} {reads : List (NodeRecord α β)} {cost : Nat}
    (h : Trace c reads d cost) (gaps : Nat → MTR.Tree (NodeRecord α β)) (base : Nat) :
    Trace (PointerGraft.cursor gaps base c) reads (PointerGraft.cursor gaps base d) cost := by
  induction h with
  | nil => exact .nil _
  | step move rest ih => exact .step (move.graft gaps base) ih
  | read atRecord rest ih => exact .read (MTR.Tree.graft_rootKey _ _ _ atRecord) ih

theorem ObservedRearranges.graft {before after : Impl α β} {budget : Nat}
    (h : ObservedRearranges before after budget)
    (gaps : Nat → MTR.Tree (NodeRecord α β)) (base : Nat)
    (ancestors : List (Pointer.Frame (NodeRecord α β))) :
    ∃ reads cost, Trace ⟨(recordTree before).graft gaps base,ancestors⟩ reads
      ⟨(recordTree after).graft gaps base,ancestors⟩ cost ∧ cost ≤ budget := by
  obtain ⟨reads,cost,trace,hcost⟩ := h []
  refine ⟨reads,cost,?_,hcost⟩
  simpa only [PointerGraft.cursor,PointerGraft.offset,PointerGraft.frames,
    PointerGraft.extend,List.nil_append,Nat.add_zero] using
    (trace.graft gaps base).extend ancestors

theorem link_grafted_charged (old : Nat) (k : α) (v : β k) (l r : Impl α β)
    (hl : l.Balanced) (hr : r.Balanced)
    (gaps : Nat → MTR.Tree (NodeRecord α β)) (base : Nat) (ancestors) :
    ∃ reads cost, Trace ⟨(recordTree (.inner old k v l r)).graft gaps base,ancestors⟩ reads
      ⟨(recordTree (link k v l r hl hr).impl).graft gaps base,ancestors⟩ cost ∧
      cost ≤ 495 * (Nat.clog 2 (l.size + 1) + Nat.clog 2 (r.size + 1)) + 76 :=
  (link_charged_log old k v l r hl hr).graft gaps base ancestors

theorem split_grafted_charged [Ord α] [LawfulEqOrd α] (x : α) (t : Impl α β)
    (ht : t.Balanced) (hf : searchResult x t = true)
    (gaps : Nat → MTR.Tree (NodeRecord α β)) (base : Nat) (ancestors) :
    ∃ reads cost, Trace ⟨(recordTree t).graft gaps base,ancestors⟩ reads
      ⟨(recordTree (splitAt x t ht hf).impl).graft gaps base,ancestors⟩ cost ∧
      cost ≤ 5730 * Nat.clog 2 (t.size + 1) :=
  (splitAt_charged_log x t ht hf).graft gaps base ancestors

end ChaCha.Paper20261030.Auxiliary.Metadata

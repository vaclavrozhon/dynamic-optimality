import TangoSquared.Paper20261030.PathPorts
import TangoSquared.Paper20261030.Rebalance

/-!
# Balancing an existing source path without changing its hanging subtrees

The source path is extracted from actual child edges. Its cached records
are rebalanced by the charged auxiliary routine, then the trace is lifted
through its original gap ports. This starts from the original decorated
source tree, rather than an assumed spine or a freshly allocated copy.
The off-path subtrees and the terminal port remain the same whole objects.
-/

namespace TangoSquared.Paper20261030.Auxiliary.Metadata

open Std.DTreeMap.Internal Std.DTreeMap.Internal.Impl

variable {κ : Type*} {β : κ → Type*}

def fromRecordTree : MTR.Tree (NodeRecord κ β) → Impl κ β
  | .empty => .leaf
  | .node l (cached,⟨key,value⟩) r => .inner cached key value (fromRecordTree l) (fromRecordTree r)

theorem recordTree_fromRecordTree (t : MTR.Tree (NodeRecord κ β)) :
    recordTree (fromRecordTree t) = t := by
  induction t with
  | empty => rfl
  | node l record r ihl ihr =>
    rcases record with ⟨cached,⟨key,value⟩⟩
    simp only [fromRecordTree,recordTree,ihl,ihr]

theorem actualSize_fromRecordTree (t : MTR.Tree (NodeRecord κ β)) :
    actualSize (fromRecordTree t) = t.size := by
  induction t with
  | empty => rfl
  | node l record r ihl ihr =>
    rcases record with ⟨cached,⟨key,value⟩⟩
    simp only [fromRecordTree,actualSize,MTR.Tree.size,ihl,ihr]

end TangoSquared.Paper20261030.Auxiliary.Metadata

namespace TangoSquared.Paper20261030.PathPorts

open Std.DTreeMap.Internal Std.DTreeMap.Internal.Impl
open ColoredStorage Auxiliary Auxiliary.Metadata

variable {α κ : Type*} {β : κ → Type*}

def auxiliary (right : NodeRecord κ β → Bool) (source : Source α (NodeRecord κ β)) :=
  rebalance (fromRecordTree (skeleton right source))

def balancedSource (right : NodeRecord κ β → Bool) (source : Source α (NodeRecord κ β)) :
    Source α (NodeRecord κ β) :=
  GapSource.encode (recordTree (auxiliary right source).impl) (port right source) 0

theorem balance_charged (right : NodeRecord κ β → Bool) (source : Source α (NodeRecord κ β))
    (ancestors : List (SourcePointer.Frame α (NodeRecord κ β))) :
    ∃ (reads : List (NodeRecord κ β)) (cost : Nat),
      SourcePointer.Trace ⟨source,ancestors⟩ reads ⟨balancedSource right source,ancestors⟩ cost ∧
      cost ≤ (990 * Nat.clog 2 ((skeleton right source).size + 1) + 81) *
        (skeleton right source).size := by
  obtain ⟨reads,cost,trace,hcost⟩ := rebalance_charged (fromRecordTree (skeleton right source)) []
  have lifted := GapSource.metadata_trace trace (port right source) 0
  have rooted : SourcePointer.Trace ⟨source,[]⟩ reads ⟨balancedSource right source,[]⟩ cost := by
    simpa only [GapSource.cursor,GapSource.frames,PointerGraft.offset,Nat.add_zero,
      recordTree_fromRecordTree,reconstruct,balancedSource,auxiliary] using lifted
  exact ⟨reads,cost,rooted.extend ancestors,by simpa only [actualSize_fromRecordTree] using hcost⟩

theorem balancedSource_leaves (right : NodeRecord κ β → Bool) (source : Source α (NodeRecord κ β)) :
    (balancedSource right source).shape.leaves = source.shape.leaves := by
  obtain ⟨reads,cost,trace,_⟩ := balance_charged right source []
  exact trace.leaves.symm

theorem auxiliary_word [Ord κ] (right : NodeRecord κ β → Bool)
    (source : Source α (NodeRecord κ β)) :
    (auxiliary right source).impl.toListModel =
      (fromRecordTree (skeleton right source)).toListModel :=
  rebalance_word _

theorem auxiliary_height (right : NodeRecord κ β → Bool) (source : Source α (NodeRecord κ β)) :
    height (auxiliary right source).impl ≤ 3 * Nat.clog 2 ((skeleton right source).size + 1) := by
  have hs : (auxiliary right source).impl.size = (skeleton right source).size :=
    (auxiliary right source).size_impl.trans (actualSize_fromRecordTree _)
  simpa only [hs] using balanced_height_log (auxiliary right source).balanced_impl

end TangoSquared.Paper20261030.PathPorts

import TangoSquared.Paper20261030.RootPreparedPairController
import TangoSquared.Paper20261030.PreparedPairHeaderController
import TangoSquared.Paper20261030.ReachedVirtualHeaderPair

set_option autoImplicit false

/-! The preparation controller followed by both actual virtual-header
reads. The continuation obtains its two headers and four boundary values
from the halted preparation state. It retains those values while a single
working finger reads the two stored virtual cursors. -/

namespace TangoSquared.Paper20261030.SecondaryDecomposition.RootPreparedPairHeaderController

open ColoredStorage SourcePointer MultiSourceProgram PrimaryHeaderController
open ObservedPreparedExposure (CachedCell)

variable {ι η G : Type*} [DecidableEq ι] [DecidableEq η] [DecidableEq G]

abbrev Inputs := PreparedPairHeaderController.Inputs

abbrev Parameters (η F : Type*) := CachedRootContinuation.Parameters η F (Option (PreparedPairController.Values η))

def select {σ τ υ F : Type*} :
    MultiSourceFinish.State σ (Option (MultiSourceFinish.State τ υ (Parameters η F))) (Parameters η F) → Option (Inputs η)
  | .second (some (active,activeId,_,some activeValues))
      (some (.second (some (incoming,incomingId,_,some incomingValues)) _)) =>
    some ⟨{active with rootId := activeId},{incoming with rootId := incomingId},activeValues,incomingValues⟩
  | _ => none

abbrev Virtual (ι η : Type*) := ReachedVirtualHeaderRead.Stored Nat (LocalColoredCompiler.LogicalRecord Cached η (Option Bool)) ι
abbrev ReadState (ι η : Type*) := ReachedVirtualHeaderPair.ReadState Nat (LocalColoredCompiler.LogicalRecord Cached η (Option Bool)) ι
abbrev PairState (ι η : Type*) := MultiSourceFinish.State (ReadState ι η) (ReadState ι η) (Option (Virtual ι η))

def origins (activeAnchor : G) : Bool → Sum (Option Bool) G
  | false => .inr activeAnchor
  | true => .inl none

def headers (input : Inputs η) : Bool → Header η
  | false => input.active
  | true => input.incoming

def source (activeAnchor : G) (count : Nat) : Option (Inputs η) →
    Program (PairState ι η) (Sum (Option Bool) G) (CachedCell ι η)
  | none => fun _ => .halt
  | some input => ReachedVirtualHeaderPair.program (origins activeAnchor) (.inl (some true))
      (fun record => record.1.2) (fun side => if side then 2 else count) (headers input)

def program (entry : Sum (Option Bool) G) (count : Nat) (hasParent : Bool)
    (activeAnchor incomingAnchor : G) (depth : Nat) :=
  MultiSourceFinish.program (RootPreparedPairController.program (ι := ι) (η := η) entry count hasParent activeAnchor incomingAnchor depth)
    select (fun _ => .first none) (source activeAnchor count)

theorem append_reads {β : Type*} (entry : Sum (Option Bool) G) (count : Nat) (hasParent : Bool)
    (activeAnchor incomingAnchor : G) (depth : Nat)
    (before middle after : Configuration (Sum (Option Bool) G) β (CachedCell ι η))
    (activeHeader incomingHeader : Header η) (activeRoot incomingRoot : η)
    (activeValues incomingValues : PreparedPairController.Values η)
    (activeVirtual incomingVirtual : Virtual ι η) {firstReads lastReads firstCost lastCost}
    (front : Run (RootPreparedPairController.program entry count hasParent activeAnchor incomingAnchor depth)
      (.first (.first .start)) before
      (.second (some (activeHeader,activeRoot,.inl none,some activeValues))
        (some (.second (some (incomingHeader,incomingRoot,.inl none,some incomingValues)) (some .done)))) middle firstReads firstCost)
    (back : Run (source activeAnchor count
      (some ⟨{activeHeader with rootId := activeRoot},{incomingHeader with rootId := incomingRoot},activeValues,incomingValues⟩))
      (.first none) middle (.second (some activeVirtual) (some (some (.done (some incomingVirtual))))) after lastReads lastCost) :
    Run (program entry count hasParent activeAnchor incomingAnchor depth)
      (.first (.first (.first .start))) before
      (.second (some ⟨{activeHeader with rootId := activeRoot},{incomingHeader with rootId := incomingRoot},activeValues,incomingValues⟩)
        (.second (some activeVirtual) (some (some (.done (some incomingVirtual)))))) after
      (firstReads++lastReads) (firstCost+lastCost) := by
  have actual := MultiSourceFinish.finish select (fun _ => (MultiSourceFinish.State.first none : PairState ι η))
    (source activeAnchor count) front back
  exact actual

end TangoSquared.Paper20261030.SecondaryDecomposition.RootPreparedPairHeaderController

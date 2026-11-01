import TangoSquared.Paper20261030.LocalClosedNeighborProgram
import TangoSquared.Paper20261030.DepartureSelection

/-! Selecting a secondary departure and its two context boundaries using
only local queries. The first query supplies the departure's stored split
interval; that observed interval supplies the next two query labels. No
split identity or boundary key is passed to the controller by a proof. -/

namespace TangoSquared.Paper20261030.SecondaryDecomposition.DepartureController

open Std Std.DTreeMap.Internal Std.DTreeMap.Internal.Impl
open ColoredStorage Auxiliary BoundaryObservations SourcePointer SourceLocalProgram

structure Result where
  departure : SeparatorPath.Entry
  lower : Option (Sigma (Tagged Payload))
  upper : Option (Sigma (Tagged Payload))

def result (request : Nat) (core : Impl Nat (Tagged Payload)) : Option Result :=
  (observedExit request (neighbors request core)).map (fun departure =>
    ⟨departure,(neighbors departure.2.1.lo core).1,(neighbors departure.2.1.hi core).2⟩)

inductive State where
  | first (state : ClosedNeighborController.State Payload)
  | lower (departure : SeparatorPath.Entry) (state : ClosedNeighborController.State Payload)
  | upper (departure : SeparatorPath.Entry) (lower : Option (Sigma (Tagged Payload)))
      (state : ClosedNeighborController.State Payload)
  | done (result : Option Result)

def finishFirst (request : Nat) : ClosedNeighborController.State Payload → State
  | .done pair => match observedExit request pair with
    | none => .done none
    | some departure => .lower departure .start
  | state => .first state

def finishLower (departure : SeparatorPath.Entry) : ClosedNeighborController.State Payload → State
  | .done pair => .upper departure pair.1 .start
  | state => .lower departure state

def finishUpper (departure : SeparatorPath.Entry) (lower : Option (Sigma (Tagged Payload))) :
    ClosedNeighborController.State Payload → State
  | .done pair => .done (some ⟨departure,lower,pair.2⟩)
  | state => .upper departure lower state

def program (request : Nat) : Program State Cached
  | .first state => (ClosedNeighborController.program request state).mapState (finishFirst request)
  | .lower departure state => (ClosedNeighborController.program departure.2.1.lo state).mapState (finishLower departure)
  | .upper departure lower state => (ClosedNeighborController.program departure.2.1.hi state).mapState (finishUpper departure lower)
  | .done _ => .halt

theorem first_code (request : Nat) (state : ClosedNeighborController.State Payload)
    (active : ClosedNeighborController.program request state ≠ .halt) :
    program request (finishFirst request state) =
      (ClosedNeighborController.program request state).mapState (finishFirst request) := by
  cases state with
  | done => exact False.elim (active rfl)
  | start | openWrite | querying | closeRead | closeWrite => rfl

theorem lower_code (request : Nat) (departure : SeparatorPath.Entry) (state : ClosedNeighborController.State Payload)
    (active : ClosedNeighborController.program departure.2.1.lo state ≠ .halt) :
    program request (finishLower departure state) =
      (ClosedNeighborController.program departure.2.1.lo state).mapState (finishLower departure) := by
  cases state with
  | done => exact False.elim (active rfl)
  | start | openWrite | querying | closeRead | closeWrite => rfl

theorem upper_code (request : Nat) (departure : SeparatorPath.Entry) (lower : Option (Sigma (Tagged Payload)))
    (state : ClosedNeighborController.State Payload)
    (active : ClosedNeighborController.program departure.2.1.hi state ≠ .halt) :
    program request (finishUpper departure lower state) =
      (ClosedNeighborController.program departure.2.1.hi state).mapState (finishUpper departure lower) := by
  cases state with
  | done => exact False.elim (active rfl)
  | start | openWrite | querying | closeRead | closeWrite => rfl

theorem query (request : Nat) {a b : Nat} (reference : DepthTree a b) (preferences : DepthSplit → Bool)
    (component : AuxiliaryComponent Nat Nat (Tagged Payload))
    (represented : PathDecomposition.Represents followsRight (source reference preferences) component) (outside) :
    ∃ reads cost, Run (program request) (.first .start) ⟨closed component,outside⟩
      (.done (result request component.core)) ⟨closed component,outside⟩ reads cost ∧
      cost ≤ 27*Nat.clog 2 (component.core.size+1)+15 := by
  obtain ⟨firstReads,firstCost,firstRun,firstBound⟩ := ClosedNeighborController.query_represented request component represented outside
  have first := firstRun.map_prefix (finishFirst request) (first_code request)
  cases selected : observedExit request (neighbors request component.core) with
  | none =>
    simp only [finishFirst,selected] at first
    refine ⟨firstReads,firstCost,?_,by omega⟩
    simpa only [result,selected,Option.map_none] using first.run (by rfl)
  | some departure =>
    simp only [finishFirst,selected] at first
    obtain ⟨lowerReads,lowerCost,lowerRun,lowerBound⟩ :=
      ClosedNeighborController.query_represented departure.2.1.lo component represented outside
    have lower := lowerRun.map_prefix (finishLower departure) (lower_code request departure)
    obtain ⟨upperReads,upperCost,upperRun,upperBound⟩ :=
      ClosedNeighborController.query_represented departure.2.1.hi component represented outside
    have upper := upperRun.map_prefix (finishUpper departure (neighbors departure.2.1.lo component.core).1)
      (upper_code request departure (neighbors departure.2.1.lo component.core).1)
    have complete := (first.append lower).append upper
    refine ⟨firstReads++lowerReads++upperReads,firstCost+lowerCost+upperCost,?_,by omega⟩
    simpa only [result,selected,Option.map_some,finishUpper] using complete.run (by rfl)

theorem head_selection {a b : Nat} (reference : DepthTree a b) (preferences : DepthSplit → Bool)
    {request depth : Nat} {after : PreferredProjection.PrefRouter Nat}
    (step : PreferredProjection.PrefRouter.HeadStep request depth (Secondary.decodeDepth reference preferences) after)
    (component : AuxiliaryComponent Nat Nat (Tagged Payload))
    (represented : PathDecomposition.Represents followsRight (source reference preferences) component) (outside) :
    ∃ pivot : PreferredSplit preferences reference,
      Secondary.decodeDepth reference (Function.update preferences pivot.split (!preferences pivot.split)) = after ∧
      ∃ reads cost, Run (program request) (.first .start) ⟨closed component,outside⟩
        (.done (some ⟨⟨pivot.split.cut,(pivot.split,preferences pivot.split)⟩,
          (neighbors pivot.split.lo component.core).1,(neighbors pivot.split.hi component.core).2⟩))
        ⟨closed component,outside⟩ reads cost ∧ cost ≤ 27*Nat.clog 2 (component.core.size+1)+15 := by
  obtain ⟨pivot,decode,selected⟩ := observed_head_selection reference preferences step component represented
  obtain ⟨reads,cost,run,bound⟩ := query request reference preferences component represented outside
  exact ⟨pivot,decode,reads,cost,by simpa only [result,selected,Option.map_some] using run,bound⟩

end TangoSquared.Paper20261030.SecondaryDecomposition.DepartureController

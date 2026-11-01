import TangoSquared.Paper20261030.LocalDepartureProgram
import TangoSquared.Paper20261030.LocalSecondaryInteriorRepair

/-! One complete secondary repair iteration. The controller first reads
the departure and interval boundaries, then passes precisely those scalar
answers to the fixed interval-repair program. The reference tree and the
preference function occur only in the correctness theorem. -/

namespace TangoSquared.Paper20261030.SecondaryDecomposition.RepairController

open PreferredProjection ColoredStorage Auxiliary BoundaryObservations PathDecomposition SourceLocalProgram

abbrev RepairState := IntervalRepairController.State (PreferenceFlipController.State Nat (DepthSplit×Bool)) Nat (DepthSplit×Bool)

def repairProgram (selection : DepartureController.Result) : Program RepairState Cached :=
  IntervalRepairController.program (selection.lower.map (fun entry => entry.1)) (selection.upper.map (fun entry => entry.1))
    (PreferenceFlipController.program selection.departure.1 (!selection.departure.2.2) togglePayload) (.opening .start)

def repairInitial (selection : DepartureController.Result) : RepairState :=
  IntervalRepairController.initial (selection.lower.map (fun entry => entry.1)) (selection.upper.map (fun entry => entry.1))
    (PreferenceFlipController.program selection.departure.1 (!selection.departure.2.2) togglePayload) (.opening .start)

inductive State where
  | selecting (state : DepartureController.State)
  | repairing (selection : DepartureController.Result) (state : RepairState)
  | done (changed : Bool)

def selecting : DepartureController.State → State
  | .done none => .done false
  | .done (some selection) => .repairing selection (repairInitial selection)
  | state => .selecting state

def repairing (selection : DepartureController.Result) : RepairState → State
  | .done => .done true
  | state => .repairing selection state

def program (request : Nat) : Program State Cached
  | .selecting state => (DepartureController.program request state).mapState selecting
  | .repairing selection state => (repairProgram selection state).mapState (repairing selection)
  | .done _ => .halt

theorem selecting_code (request : Nat) (state : DepartureController.State)
    (active : DepartureController.program request state ≠ .halt) :
    program request (selecting state) = (DepartureController.program request state).mapState selecting := by
  cases state with
  | first | lower | upper => rfl
  | done result => cases result <;> exact False.elim (active rfl)

theorem repairing_code (request : Nat) (selection : DepartureController.Result) (state : RepairState)
    (active : repairProgram selection state ≠ .halt) :
    program request (repairing selection state) = (repairProgram selection state).mapState (repairing selection) := by
  cases state with
  | bare | «prefix» | suffix | middle => rfl
  | done => exact False.elim (active rfl)

theorem repairing_initial (selection : DepartureController.Result) :
    repairing selection (repairInitial selection) = State.repairing selection (repairInitial selection) := by
  rcases selection with ⟨departure,lower,upper⟩
  cases lower <;> cases upper <;> rfl

theorem head_step {a b : Nat} (reference : DepthTree a b) (preferences : DepthSplit → Bool)
    {request depth : Nat} {after : PrefRouter Nat}
    (step : PrefRouter.HeadStep request depth (Secondary.decodeDepth reference preferences) after)
    (component : AuxiliaryComponent Nat Nat (Tagged Payload))
    (represented : Represents followsRight (source reference preferences) component) (outside) :
    ∃ (pivot : PreferredSplit preferences reference) (out : AuxiliaryComponent Nat Nat (Tagged Payload)),
      Secondary.decodeDepth reference (Function.update preferences pivot.split (!preferences pivot.split)) = after ∧
      Represents followsRight (source reference (Function.update preferences pivot.split (!preferences pivot.split))) out ∧
      ∃ reads cost, Run (program request) (.selecting (.first .start)) ⟨closed component,outside⟩ (.done true)
        ⟨closed out,outside⟩ reads cost ∧
        cost ≤ 130857*Nat.clog 2 ((LocalReferences.depthReference reference).height+1)+973 := by
  obtain ⟨pivot,decoded,queryReads,queryCost,queryRun,queryBound⟩ :=
    DepartureController.head_selection reference preferences step component represented outside
  let selection : DepartureController.Result :=
    ⟨⟨pivot.split.cut,(pivot.split,preferences pivot.split)⟩,
      (neighbors pivot.split.lo component.core).1,(neighbors pivot.split.hi component.core).2⟩
  have selected := queryRun.map_prefix selecting (selecting_code request)
  obtain ⟨out,outRep,repairReads,repairCost,repairRun,repairBound⟩ := flip_descendant_controller
    pivot.lo_le_cut pivot.cut_lt_hi pivot.left pivot.right reference preferences pivot.below component represented outside
  have repaired := repairRun.map_prefix (repairing selection) (repairing_code request selection)
  change Steps (program request) (repairing selection (repairInitial selection))
    ⟨closed component,outside⟩ (.done true) ⟨closed out,outside⟩ repairReads repairCost at repaired
  rw [repairing_initial] at repaired
  have full := selected.append repaired
  have size := represented_size reference preferences component represented
  have rank := Nat.clog_monotone 2 (Nat.add_le_add_right size 1)
  exact ⟨pivot,out,decoded,outRep,_,_,full.run rfl,by omega⟩

theorem terminal {a b : Nat} (reference : DepthTree a b) (preferences : DepthSplit → Bool)
    (component : AuxiliaryComponent Nat Nat (Tagged Payload))
    (represented : Represents followsRight (source reference preferences) component) (outside) :
    ∃ reads cost, Run (program (Secondary.decodeDepth reference preferences).terminal) (.selecting (.first .start))
      ⟨closed component,outside⟩ (.done false) ⟨closed component,outside⟩ reads cost ∧
      cost ≤ 27*Nat.clog 2 (component.core.size+1)+15 := by
  have stopped := observed_terminal_none reference preferences component represented
  obtain ⟨reads,cost,run,bound⟩ := DepartureController.query (Secondary.decodeDepth reference preferences).terminal
    reference preferences component represented outside
  have selected := run.map_prefix selecting (selecting_code _)
  simp only [DepartureController.result,stopped,Option.map_none,selecting] at selected
  exact ⟨reads,cost,selected.run rfl,bound⟩

end TangoSquared.Paper20261030.SecondaryDecomposition.RepairController

import TangoSquared.Paper20261030.PrimaryEntryProgram
import TangoSquared.Paper20261030.MultiSourceRecenter

/-! Reusable component entry. Only one selected physical finger must
already reach the component root. Three charged copies recenter the
registers; a root read obtains the logical presence bits. Hidden physical
registers may retain pointers. The existing entry and component controller
then run under the checked presence-mask adapter.
-/

namespace TangoSquared.Paper20261030.PrimaryReentryController

open ColoredStorage SourcePointer SourcePositions MultiSourceProgram ForestConnector.ThreeColors

variable {α ρ σ η : Type*}

def bits (header : PrimaryHeaderController.Header η) : Option Bool → Bool
  | none => true
  | some true => header.leftWing
  | some false => header.rightWing

inductive State (σ ρ η : Type*) where
  | resetting (destinations : List (Option Bool))
  | reading
  | running (header : PrimaryHeaderController.Header η)
      (phase : MultiSourceMask.State (PrimaryEntryController.State σ ρ η) (Option Bool))
  | blocked

def reset : List (Option Bool) → State σ ρ η
  | [] => .reading
  | destinations => .resetting destinations

def program (origin : Option Bool) (height : Nat) (request : Int) (start : η → σ)
    (component : Nat → Program σ (Option Bool) (List ρ)) :
    Program (State σ ρ η) (Option Bool) (PrimaryHeaderController.Record (List ρ) η)
  | .resetting [] => .halt
  | .resetting (destination::rest) => .copy destination origin (reset rest)
  | .reading => .read none (fun observed => match observed with
      | some ((_,some header),_) => .running header (bits header,.start)
      | _ => .blocked)
  | .running header phase =>
      (MultiSourceMask.program (PrimaryEntryController.program height request start component) phase).mapState (.running header)
  | .blocked => .halt

theorem reset_code (origin : Option Bool) (height : Nat) (request : Int) (start : η → σ)
    (component : Nat → Program σ (Option Bool) (List ρ)) (destinations : List (Option Bool))
    (active : MultiSourceRecenter.program origin (ρ := PrimaryHeaderController.Record (List ρ) η) destinations ≠ .halt) :
    program origin height request start component (reset destinations) =
      (MultiSourceRecenter.program origin destinations).mapState reset := by
  cases destinations with
  | nil => exact False.elim (active rfl)
  | cons => rfl

theorem dispatch (origin : Option Bool) (height : Nat) (request : Int) (start : η → σ)
    (component : Nat → Program σ (Option Bool) (List ρ))
    (forest : ProjectionForest.State (Option Bool) α ρ) (headerTree : Source α (List ρ))
    (rooted : ∀ q current, forest q = some current → current.ancestors = [])
    (header : PrimaryHeaderController.Header η)
    (leftWing : header.leftWing = (forest (some true)).isSome)
    (rightWing : header.rightWing = (forest (some false)).isSome)
    (config : Configuration (Option Bool) α (PrimaryHeaderController.Record (List ρ) η))
    (validConfig : WellFormed config) (atRoot : config.fingers origin = some [])
    (tree : config.tree.mapRecords Prod.fst = (configuration forest ⟨headerTree,[]⟩).tree)
    (stored : config.tree.rootRecord.2 = some header)
    (validRequest : Dyadic.ValidKey height request) (validBottom : Dyadic.ValidKey height header.bottom)
    {last : σ} {target : Configuration (Option Bool) α (List ρ)} {reads cost}
    (run : Run (component (Dyadic.lcaDepth height request header.bottom)) (start header.rootId)
      (configuration forest ⟨headerTree,[]⟩) last target reads cost) :
    ∃ finalBits actualTarget actualReads actualCost,
      Run (program origin height request start component) (reset MultiSourceRecenter.three) config
        (.running header (finalBits,.running header (.ready (.running last)))) actualTarget actualReads actualCost ∧
      (actualTarget.mask finalBits).mapRecords Prod.fst = target ∧ WellFormed actualTarget ∧
      actualTarget.tree.inventory Prod.snd = config.tree.inventory Prod.snd ∧ actualCost ≤ 2*cost+15 := by
  let centered : Configuration (Option Bool) α (PrimaryHeaderController.Record (List ρ) η) :=
    ⟨config.tree,fun _ => some []⟩
  have resetRun : Run (MultiSourceRecenter.program origin) MultiSourceRecenter.three config [] centered [] 3 := by
    simpa only [atRoot] using MultiSourceRecenter.three_run origin config
  have centeredValid : WellFormed centered := resetRun.wellFormed validConfig
  have entry : (centered.mask (bits header)).mapRecords Prod.fst = entryConfiguration forest headerTree := by
    simp only [centered,Configuration.mask,Configuration.mapRecords,entryConfiguration,tree]
    congr 1
    funext finger
    cases finger with
    | none => simp [bits]
    | some side => cases side <;> simp [bits,leftWing,rightWing]
  obtain ⟨logicalTarget,logicalReads,logicalCost,logicalRun,logicalErases,metadata,bound⟩ :=
    PrimaryEntryController.dispatch height request start component forest headerTree rooted header leftWing rightWing
      (centered.mask (bits header)) entry stored validRequest validBottom run
  obtain ⟨finalBits,actualTarget,actualReads,actualRun,maskEq,actualValid⟩ :=
    MultiSourceMask.compile_run logicalRun (bits header) centered centeredValid rfl
  let code := program origin height request start component
  have first := resetRun.map_prefix (target := code) reset (reset_code origin height request start component)
  have read : Step code .reading centered (.running header (bits header,.start)) centered
      (some (none,config.tree.rootRecord)) := by
    have raw := Step.readSome (program := code) (state := .reading) (config := centered)
      (position := []) (current := ⟨config.tree,[]⟩)
      (next := fun observed => match observed with
        | some ((_,some header),_) => State.running header (bits header,.start)
        | _ => .blocked)
      rfl rfl rfl
    cases value : config.tree.rootRecord with
    | mk routing metadata =>
      have same : metadata = some header := by simpa only [value] using stored
      simpa only [value,same] using raw
  have rest := actualRun.map_prefix (target := code) (State.running header) (fun _ _ => rfl)
  have whole := ((first.append read.prefix).append rest).run (by
    change (MultiSourceMask.program (PrimaryEntryController.program height request start component)
      (finalBits,.running header (.ready (.running last)))).mapState (State.running header) = .halt
    rw [actualRun.halted]
    rfl)
  refine ⟨finalBits,actualTarget,_,_,whole,maskEq ▸ logicalErases,actualValid,?_,by omega⟩
  have sameTree := congrArg Configuration.tree maskEq
  change actualTarget.tree = logicalTarget.tree at sameTree
  rw [sameTree]
  exact metadata

end TangoSquared.Paper20261030.PrimaryReentryController

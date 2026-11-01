import TangoSquared.Paper20261030.PrimaryReentryProgram
import TangoSquared.Paper20261030.PrimaryComponentHeaderRefresh
import TangoSquared.Paper20261030.MultiSourceFinish

/-! A component-entry continuation which refreshes the primary root
cache before returning. It extracts the identifier from the halted
component controller's scalar registers and reuses the header already
loaded at entry. Its local overhead beyond reusable entry is at most six
operations. The caller supplies the final component-representation proof,
not a tree or an identifier to the running program.
-/

namespace TangoSquared.Paper20261030.PrimaryRefreshingReentry

open ColoredStorage SourcePointer MultiSourceProgram PrimaryHeaderController
open ForestConnector.ThreeColors

variable {α ρ η σ : Type*}

structure Context (η : Type*) where
  header : Header η
  rootId : η
  active : Option Bool → Bool

abbrev Parameters (η : Type*) := Option (Context η)
abbrev RefreshState (ρ η : Type*) := Option (RootRecordTour.State (Record (List ρ) η))
abbrev State (σ ρ η : Type*) := MultiSourceFinish.State
  (PrimaryReentryController.State σ ρ η) (RefreshState ρ η) (Parameters η)

def select (rootId : σ → Option η) : PrimaryReentryController.State σ ρ η → Parameters η
  | .running header (active, .running _ (.ready (.running last))) =>
      (rootId last).map (fun id => ⟨header,id,active⟩)
  | _ => none

def initial : Parameters η → RefreshState ρ η
  | none => none
  | some context => some (RootRecordTour.ascend (PrimaryHeaderRefresh.path context.header).length)

def target : Parameters η → Program (RefreshState ρ η) (Option Bool) (Record (List ρ) η)
  | none => fun _ => .halt
  | some context => PrimaryHeaderRefresh.program none context.header context.rootId (PrimaryHeaderRefresh.path context.header)

def program (origin : Option Bool) (height : Nat) (request : Int) (start : η → σ)
    (component : Nat → Program σ (Option Bool) (List ρ)) (rootId : σ → Option η) :
    Program (State σ ρ η) (Option Bool) (Record (List ρ) η) :=
  MultiSourceFinish.program (PrimaryReentryController.program origin height request start component)
    (select rootId) initial target

theorem append_refresh (origin : Option Bool) (height : Nat) (request : Int) (start : η → σ)
    (component : Nat → Program σ (Option Bool) (List ρ)) (rootId : σ → Option η)
    (header : Header η) (freshId : η) (last : σ) (scalar : rootId last = some freshId)
    (active : Option Bool → Bool)
    (before middle : Configuration (Option Bool) α (Record (List ρ) η))
    (reads : List (Option Bool × Record (List ρ) η)) (cost : Nat)
    (front : Run (PrimaryReentryController.program origin height request start component)
      (PrimaryReentryController.reset MultiSourceRecenter.three) before
      (.running header (active,.running header (.ready (.running last)))) middle reads cost)
    (valid : WellFormed middle)
    (forest : ProjectionForest.State (Option Bool) α ρ) (headerTree : Source α (List ρ))
    (leftWing : header.leftWing = (forest (some true)).isSome)
    (rightWing : header.rightWing = (forest (some false)).isSome)
    (represented : (middle.mask active).mapRecords Prod.fst = configuration forest ⟨headerTree,[]⟩) :
    ∃ final actualReads actualCost,
      Run (program origin height request start component rootId)
        (MultiSourceFinish.enter (PrimaryReentryController.program origin height request start component)
          (select rootId) initial (PrimaryReentryController.reset MultiSourceRecenter.three)) before
        (.second (some ⟨header,freshId,active⟩) (some .done)) final actualReads actualCost ∧
      final.mapRecords Prod.fst = middle.mapRecords Prod.fst ∧
      final.tree.rootRecord.2 = some {header with rootId := freshId} ∧
      WellFormed final ∧ actualCost ≤ cost+6 := by
  obtain ⟨final,refreshReads,refreshCost,refresh,erases,stored,finalValid,bound⟩ :=
    PrimaryHeaderRefresh.component_refresh header freshId forest headerTree leftWing rightWing active middle represented valid
  have selected : select (ρ := ρ) rootId (.running header (active,.running header (.ready (.running last)))) = some ⟨header,freshId,active⟩ := by
    simp only [select,scalar,Option.map_some]
  have back : Run (target (select (ρ := ρ) rootId (.running header (active,.running header (.ready (.running last))))))
      (initial (select (ρ := ρ) rootId (.running header (active,.running header (.ready (.running last))))))
      middle (some .done) final refreshReads refreshCost := by
    simpa only [selected,target,initial] using refresh
  have actual := MultiSourceFinish.finish (select (ρ := ρ) rootId) initial target front back
  rw [selected] at actual
  exact ⟨final,_,_,actual,erases,stored,finalValid,by omega⟩

end TangoSquared.Paper20261030.PrimaryRefreshingReentry

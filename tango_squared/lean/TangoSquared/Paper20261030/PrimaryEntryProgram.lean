import TangoSquared.Paper20261030.PrimaryHeaderProgram
import TangoSquared.Paper20261030.MultiSourceEntry
import TangoSquared.Paper20261030.ThreeColorEntry

/-! Component entry controlled by an actual read of its root metadata.
The loaded wing bits determine all downward moves, and the loaded bottom
key determines the secondary request. Used fingers initially point to
the component root; unused registers are absent. Resetting registers when
arriving from a different component is a separate primary-loop task.
-/

namespace TangoSquared.Paper20261030.PrimaryEntryController

open ColoredStorage SourcePointer SourcePositions MultiSourceProgram ForestConnector.ThreeColors

variable {α ρ σ η : Type*}

abbrev State (σ ρ η : Type*) :=
  PrimaryHeaderController.State (MultiSourceEntry.State σ (Option Bool)) (Option Bool) (List ρ) η

def initial (start : η → σ) (header : PrimaryHeaderController.Header η) : MultiSourceEntry.State σ (Option Bool) :=
  MultiSourceEntry.enter (start header.rootId) (entrySchedule header.leftWing header.rightWing)

def program (height : Nat) (request : Int) (start : η → σ)
    (component : Nat → Program σ (Option Bool) (List ρ)) :
    Program (State σ ρ η) (Option Bool) (PrimaryHeaderController.Record (List ρ) η) :=
  PrimaryHeaderController.program height request none (initial start)
    (fun depth => MultiSourceEntry.program (component depth))

theorem dispatch (height : Nat) (request : Int) (start : η → σ)
    (component : Nat → Program σ (Option Bool) (List ρ))
    (forest : ProjectionForest.State (Option Bool) α ρ) (headerTree : Source α (List ρ))
    (rooted : ∀ q current, forest q = some current → current.ancestors = [])
    (header : PrimaryHeaderController.Header η)
    (leftWing : header.leftWing = (forest (some true)).isSome)
    (rightWing : header.rightWing = (forest (some false)).isSome)
    (config : Configuration (Option Bool) α (PrimaryHeaderController.Record (List ρ) η))
    (entry : config.mapRecords Prod.fst = entryConfiguration forest headerTree)
    (stored : config.tree.rootRecord.2 = some header)
    (validRequest : Dyadic.ValidKey height request) (validBottom : Dyadic.ValidKey height header.bottom)
    {last : σ} {target : Configuration (Option Bool) α (List ρ)} {reads cost}
    (run : Run (component (Dyadic.lcaDepth height request header.bottom)) (start header.rootId)
      (configuration forest ⟨headerTree,[]⟩) last target reads cost) :
    ∃ actualTarget actualReads actualCost,
      Run (program height request start component) .start config
        (.running header (.ready (.running last))) actualTarget actualReads actualCost ∧
      actualTarget.mapRecords Prod.fst = target ∧
      actualTarget.tree.inventory Prod.snd = config.tree.inventory Prod.snd ∧ actualCost ≤ 2*cost+11 := by
  have evaluate := entry_execute forest headerTree rooted
  rw [← entry,← leftWing,← rightWing] at evaluate
  have entered := MultiSourceEntry.entry_run _ _ _ _ evaluate run
  have present : config.fingers none = some [] := by
    have equal := congrArg (fun c => c.fingers none) entry
    simpa only [Configuration.mapRecords,entryConfiguration,ite_true] using equal
  obtain ⟨target,actualReads,actualCost,actual,erases,metadata,bounded⟩ :=
    PrimaryHeaderController.dispatch height request none (initial start)
      (fun depth => MultiSourceEntry.program (component depth)) config [] ⟨config.tree,[]⟩ present rfl
      header stored validRequest validBottom entered
  have scheduleBound := entrySchedule_bound header.leftWing header.rightWing
  exact ⟨target,actualReads,actualCost,actual,erases,metadata,by omega⟩

end TangoSquared.Paper20261030.PrimaryEntryController

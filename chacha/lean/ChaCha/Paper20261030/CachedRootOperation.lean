import ChaCha.Paper20261030.PrimaryHeaderRefreshAt
import ChaCha.Paper20261030.MultiSourceFinish

set_option autoImplicit false

/-! A reached root cache supplies the parameters of an actual shared-tree
operation. Its final scalar state supplies the new logical root id. One
read loads the header; the existing metadata compiler preserves caches
through the body; two operations refresh the reached output root. -/

namespace ChaCha.Paper20261030.MultiSourceSingleCursor

open ColoredStorage SourcePointer SourcePositions MultiSourceProgram

variable {α ρ τ F : Type*} [DecidableEq F]

theorem lift_represents (erase : ρ → τ) (finger : F) (current : Cursor α τ)
    (config : Configuration F α ρ) (represented : Represents finger current (config.mapRecords erase)) :
    ∃ actual, Represents finger actual config ∧ actual.mapRecords erase = current := by
  have reached : locate (config.tree.mapRecords erase) (address current) = some current := by
    change locate (config.mapRecords erase).tree (address current) = some current
    rw [represented.1]
    exact locate_cursor current
  obtain ⟨actual,found,same⟩ := lift_locate erase config.tree (address current) current reached
  refine ⟨actual,⟨(locate_tree found).symm,?_⟩,same⟩
  have position := represented.2
  rw [← same,address_mapRecords] at position
  exact position

end ChaCha.Paper20261030.MultiSourceSingleCursor

namespace ChaCha.Paper20261030.CachedRootOperation

open ColoredStorage SourcePointer SourcePositions MultiSourceProgram PrimaryHeaderController

variable {α ρ η F σ : Type*} [DecidableEq F]

abbrev FrontState (σ F ρ η : Type*) :=
  MultiSourceReadDispatch.State (Header η) (MultiSourceAugment.State σ F ρ (Option (Header η)))
abbrev Parameters (η F : Type*) := Option (Header η × η × F)
abbrev RefreshState (ρ η : Type*) := Option (RootRecordTour.State (Record ρ η))

def front (entry : F) (source : Header η → Program σ F ρ) (initial : Header η → σ) :=
  MultiSourceReadDispatch.program entry Prod.snd (fun header => .ready (initial header))
    (fun header => MultiSourceAugment.program (source header))

def select (rootId : σ → Option η) (exit : σ → F) : FrontState σ F ρ η → Parameters η F
  | .running header (.ready last) => (rootId last).map (fun fresh => (header,fresh,exit last))
  | _ => none

def refreshInitial : Parameters η F → RefreshState ρ η
  | none => none
  | some _ => some .reading

def refresh : Parameters η F → Program (RefreshState ρ η) F (Record ρ η)
  | none => fun _ => .halt
  | some (header,fresh,finger) => PrimaryHeaderRefresh.program finger header fresh []

def program (entry : F) (source : Header η → Program σ F ρ) (initial : Header η → σ)
    (rootId : σ → Option η) (exit : σ → F) :=
  MultiSourceFinish.program (front entry source initial) (select rootId exit) refreshInitial refresh

theorem execute (entry : F) (source : Header η → Program σ F ρ) (initial : Header η → σ)
    (rootId : σ → Option η) (exit : σ → F)
    (config : Configuration F α (Record ρ η)) (current : Cursor α (Record ρ η))
    (atRoot : MultiSourceSingleCursor.Represents entry current config) (valid : WellFormed config)
    (header : Header η) (stored : current.focus.rootRecord.2 = some header)
    {last : σ} {target : Configuration F α ρ} {reads cost}
    (body : Run (source header) (initial header) (config.mapRecords Prod.fst) last target reads cost)
    (fresh : η) (known : rootId last = some fresh) (returned : Cursor α ρ)
    (atOutput : MultiSourceSingleCursor.Represents (exit last) returned target) :
    ∃ final actualReads actualCost, ∃ reached : Cursor α (Record ρ η),
      Run (program entry source initial rootId exit) (.first .start) config
        (.second (some (header,fresh,exit last)) (some .done)) final actualReads actualCost ∧
      final.mapRecords Prod.fst = target ∧ reached.mapRecords Prod.fst = returned ∧
      MultiSourceSingleCursor.Represents (exit last) (PrimaryHeaderRefresh.refreshed header fresh reached) final ∧
      (PrimaryHeaderRefresh.refreshed header fresh reached).focus.rootRecord.2 = some {header with rootId := fresh} ∧
      WellFormed final ∧ actualCost ≤ 2*cost+3 := by
  obtain ⟨middle,bodyReads,bodyCost,compiled,erases,_,bound⟩ := MultiSourceAugment.compile_run body config rfl
  have reachedRoot : locate config.tree (address current) = some current := by
    rw [atRoot.1]
    exact locate_cursor current
  have dispatched := MultiSourceReadDispatch.dispatch entry Prod.snd (fun h => .ready (initial h))
    (fun h => MultiSourceAugment.program (source h)) config (address current) current atRoot.2 reachedRoot
    header stored compiled
  have erasedOutput : MultiSourceSingleCursor.Represents (exit last) returned (middle.mapRecords Prod.fst) := erases.symm ▸ atOutput
  obtain ⟨reached,positioned,same⟩ := MultiSourceSingleCursor.lift_represents Prod.fst (exit last) returned middle erasedOutput
  obtain ⟨final,refreshReads,refreshed,refreshErases,finalRep,finalValid⟩ :=
    PrimaryHeaderRefresh.at_cursor (exit last) header fresh reached middle positioned (dispatched.wellFormed valid)
  have selection : select (ρ := ρ) rootId exit (.running header (.ready last)) = some (header,fresh,exit last) := by
    simp only [select,known,Option.map_some]
  have back : Run (refresh (select (ρ := ρ) rootId exit (.running header (.ready last))))
      (refreshInitial (select (ρ := ρ) rootId exit (.running header (.ready last)))) middle (some .done) final refreshReads 2 := by
    simpa only [selection,refresh,refreshInitial] using refreshed
  have actual := MultiSourceFinish.finish (select (ρ := ρ) rootId exit) refreshInitial refresh dispatched back
  rw [selection] at actual
  exact ⟨final,_,_,reached,actual,refreshErases.trans erases,same,finalRep,
    PrimaryHeaderRefresh.refreshed_header header fresh reached,finalValid,by omega⟩

end ChaCha.Paper20261030.CachedRootOperation

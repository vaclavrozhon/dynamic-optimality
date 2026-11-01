import TangoSquared.Paper20261030.CachedRootMetadataAssociation

set_option autoImplicit false

/-! A cache refresh that retains the actual scalar data needed by the
next phase. The selector `keep` is evaluated on the component's halted
state, so boundary observations survive refresh without an extra read or
any access to a ghost tree. The selected data must later satisfy the
controller's workspace bound. -/

namespace TangoSquared.Paper20261030.CachedRootContinuation

open ColoredStorage SourcePointer SourcePositions MultiSourceProgram PrimaryHeaderController
open CachedRootOperation (front FrontState RefreshState RetainedMetadata)

variable {α ρ ι η F σ κ : Type*} [DecidableEq F]

abbrev Parameters (η F κ : Type*) := Option (Header η × η × F × κ)

def select (rootId : σ → Option η) (exit : σ → F) (keep : σ → κ) : FrontState σ F ρ η → Parameters η F κ
  | .running header (.ready last) => (rootId last).map (fun fresh => (header,fresh,exit last,keep last))
  | _ => none

def refreshInitial : Parameters η F κ → RefreshState ρ η
  | none => none
  | some _ => some .reading

def refresh : Parameters η F κ → Program (RefreshState ρ η) F (Record ρ η)
  | none => fun _ => .halt
  | some (header,fresh,finger,_) => PrimaryHeaderRefresh.program finger header fresh []

def program (entry : F) (source : Header η → Program σ F ρ) (initial : Header η → σ)
    (rootId : σ → Option η) (exit : σ → F) (keep : σ → κ) :=
  MultiSourceFinish.program (front entry source initial) (select rootId exit keep) refreshInitial refresh

theorem execute_with_metadata (identify : ρ → ι) (entry : F) (source : Header η → Program σ F ρ) (initial : Header η → σ)
    (rootId : σ → Option η) (exit : σ → F) (keep : σ → κ)
    (config : Configuration F α (Record ρ η)) (current : Cursor α (Record ρ η))
    (atRoot : MultiSourceSingleCursor.Represents entry current config) (valid : WellFormed config)
    (header : Header η) (stored : current.focus.rootRecord.2 = some header)
    {last : σ} {target : Configuration F α ρ} {reads cost}
    (body : Run (source header) (initial header) (config.mapRecords Prod.fst) last target reads cost)
    (fresh : η) (known : rootId last = some fresh) (returned : Cursor α ρ)
    (atOutput : MultiSourceSingleCursor.Represents (exit last) returned target)
    (order : target.tree.inorderLabels identify = (config.mapRecords Prod.fst).tree.inorderLabels identify)
    (unique : (config.tree.inventory (identify ∘ Prod.fst)).Nodup) :
    ∃ final actualReads actualCost, ∃ reached : Cursor α (Record ρ η),
      Run (program entry source initial rootId exit keep) (.first .start) config
        (.second (some (header,fresh,exit last,keep last)) (some .done)) final actualReads actualCost ∧
      final.mapRecords Prod.fst = target ∧ reached.mapRecords Prod.fst = returned ∧
      MultiSourceSingleCursor.Represents (exit last) (PrimaryHeaderRefresh.refreshed header fresh reached) final ∧
      (PrimaryHeaderRefresh.refreshed header fresh reached).focus.rootRecord.2 = some {header with rootId := fresh} ∧
      WellFormed final ∧
      RetainedMetadata identify (identify returned.focus.rootRecord) config.tree final.tree ∧
      actualCost ≤ 2*cost+3 := by
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
  have selection : select (ρ := ρ) rootId exit keep (.running header (.ready last)) = some (header,fresh,exit last,keep last) := by
    simp only [select,known,Option.map_some]
  have back : Run (refresh (select (ρ := ρ) rootId exit keep (.running header (.ready last))))
      (refreshInitial (select (ρ := ρ) rootId exit keep (.running header (.ready last)))) middle (some .done) final refreshReads 2 := by
    simpa only [selection,refresh,refreshInitial] using refreshed
  have actual := MultiSourceFinish.finish (select (ρ := ρ) rootId exit keep) refreshInitial refresh dispatched back
  rw [selection] at actual
  refine ⟨final,_,_,reached,actual,refreshErases.trans erases,same,finalRep,
    PrimaryHeaderRefresh.refreshed_header header fresh reached,finalValid,?_,by omega⟩
  have paired := MultiSourceAugment.paired_inventory identify body order config rfl compiled
  intro old oldPresent new newPresent equal different
  let predicate : Record ρ η → Prop := fun record => identify record.1 = identify old.1 → record.2 = old.2
  have middleInvariant : SourceRecordPredicate.Holds predicate middle.tree := by
    intro record member identity
    exact Source.metadata_of_paired_inventory (identify ∘ Prod.fst) Prod.snd config.tree middle.tree unique paired
      old record oldPresent member identity
  have reachedIdentity : identify reached.focus.rootRecord.1 = identify returned.focus.rootRecord := by
    have roots := congrArg (fun cursor : Cursor α ρ => identify cursor.focus.rootRecord) same
    simpa only [Cursor.mapRecords,Source.mapRecords_root] using roots
  have refreshedInvariant : SourceRecordPredicate.Holds predicate (PrimaryHeaderRefresh.refreshed header fresh reached).tree := by
    apply SourceRecordPredicate.write predicate reached (PrimaryHeaderRefresh.edit header fresh reached.focus.rootRecord)
      (positioned.1 ▸ middleInvariant)
    intro equality
    apply False.elim
    apply different
    exact equality.symm.trans reachedIdentity
  rw [finalRep.1] at newPresent
  exact refreshedInvariant new newPresent equal

end TangoSquared.Paper20261030.CachedRootContinuation

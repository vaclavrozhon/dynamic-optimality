import TangoSquared.Paper20261030.PrimaryHeaderRefreshAt
import TangoSquared.Paper20261030.SourceInorderMetadataPairs
import TangoSquared.Paper20261030.SourceRecordPredicate
import TangoSquared.Paper20261030.MultiSourceFinish
import TangoSquared.Paper20261030.MultiSourceRecordMap
import TangoSquared.Paper20261030.CachedAnchorHandoff

set_option autoImplicit false

/-! Install two computed component headers at distinct reached physical
vertices. Four charged operations suffice. Physical-id uniqueness proves
that the second write retains the cache installed by the first write. -/

namespace TangoSquared.Paper20261030.PrimaryHeaderPairRefresh

open ColoredStorage SourcePointer Structural MultiSourceProgram PrimaryHeaderController

variable {α ρ ι η F : Type*} [DecidableEq F]

def program (first second : F) (firstHeader secondHeader : Header η) :=
  MultiSourceFinish.program (PrimaryHeaderRefresh.program (ρ := ρ) first firstHeader firstHeader.rootId [])
    (fun _ => ()) (fun _ => some RootRecordTour.State.reading)
    (fun _ => PrimaryHeaderRefresh.program second secondHeader secondHeader.rootId [])

set_option backward.isDefEq.respectTransparency false in
theorem execute (identify : ρ → ι) (first second : F) (firstHeader secondHeader : Header η)
    (config : Configuration F α (Record ρ η)) (firstCurrent secondCurrent : Cursor α (Record ρ η))
    (firstRep : MultiSourceSingleCursor.Represents first firstCurrent config)
    (secondRep : MultiSourceSingleCursor.Represents second secondCurrent config)
    (valid : WellFormed config) (unique : (config.tree.inventory (identify ∘ Prod.fst)).Nodup)
    (distinct : identify firstCurrent.focus.rootRecord.1 ≠ identify secondCurrent.focus.rootRecord.1) :
    ∃ target reads firstReached secondReached,
      Run (program (ρ := ρ) first second firstHeader secondHeader) (.first (some .reading)) config
        (.second () (some .done)) target reads 4 ∧
      target.mapRecords Prod.fst = config.mapRecords Prod.fst ∧
      MultiSourceSingleCursor.Represents first firstReached target ∧
      MultiSourceSingleCursor.Represents second secondReached target ∧
      firstReached.mapRecords Prod.fst = firstCurrent.mapRecords Prod.fst ∧
      secondReached.mapRecords Prod.fst = secondCurrent.mapRecords Prod.fst ∧
      firstReached.focus.rootRecord.2 = some firstHeader ∧ secondReached.focus.rootRecord.2 = some secondHeader ∧
      WellFormed target := by
  obtain ⟨middle,firstReads,front,firstErases,firstAtRoot,middleValid⟩ :=
    PrimaryHeaderRefresh.at_cursor first firstHeader firstHeader.rootId firstCurrent config firstRep valid
  let firstUpdated := PrimaryHeaderRefresh.refreshed firstHeader firstHeader.rootId firstCurrent
  have firstHeaderStored : firstUpdated.focus.rootRecord.2 = some firstHeader := by
    exact PrimaryHeaderRefresh.refreshed_header firstHeader firstHeader.rootId firstCurrent
  have firstRaw := PrimaryHeaderRefresh.refreshed_erases firstHeader firstHeader.rootId firstCurrent
  have secondInMiddle : MultiSourceSingleCursor.Represents second (secondCurrent.mapRecords Prod.fst) (middle.mapRecords Prod.fst) :=
    firstErases.symm ▸ secondRep.mapRecords Prod.fst
  obtain ⟨secondMiddle,secondAtRoot,secondRaw⟩ := MultiSourceSingleCursor.lift_represents Prod.fst second
    (secondCurrent.mapRecords Prod.fst) middle secondInMiddle
  obtain ⟨target,secondReads,back,secondErases,secondFinalRep,targetValid⟩ :=
    PrimaryHeaderRefresh.at_cursor second secondHeader secondHeader.rootId secondMiddle middle secondAtRoot middleValid
  let secondUpdated := PrimaryHeaderRefresh.refreshed secondHeader secondHeader.rootId secondMiddle
  have secondHeaderStored : secondUpdated.focus.rootRecord.2 = some secondHeader := by
    exact PrimaryHeaderRefresh.refreshed_header secondHeader secondHeader.rootId secondMiddle
  have firstInTarget : MultiSourceSingleCursor.Represents first (firstUpdated.mapRecords Prod.fst) (target.mapRecords Prod.fst) :=
    secondErases.symm ▸ firstAtRoot.mapRecords Prod.fst
  obtain ⟨firstReached,firstFinalRep,firstFinalRaw⟩ := MultiSourceSingleCursor.lift_represents Prod.fst first
    (firstUpdated.mapRecords Prod.fst) target firstInTarget
  have middleUnique : (middle.tree.inventory (identify ∘ Prod.fst)).Nodup := by
    rw [← mapRecords_inventory Prod.fst identify middle.tree]
    change ((middle.mapRecords Prod.fst).tree.inventory identify).Nodup
    rw [firstErases]
    change ((config.tree.mapRecords Prod.fst).inventory identify).Nodup
    rw [mapRecords_inventory]
    exact unique
  let predicate : Record ρ η → Prop := fun record => identify record.1 = identify firstUpdated.focus.rootRecord.1 → record.2 = some firstHeader
  have firstPresent : firstUpdated.focus.rootRecord ∈ middle.tree.inventory id := by
    rw [firstAtRoot.1]
    exact Multiset.mem_of_le (inventory_le_plug id firstUpdated.focus firstUpdated.ancestors) (root_mem_inventory id firstUpdated.focus)
  have middleInvariant : SourceRecordPredicate.Holds predicate middle.tree := by
    intro record member identity
    exact (Source.metadata_of_paired_inventory (identify ∘ Prod.fst) Prod.snd middle.tree middle.tree middleUnique rfl
      firstUpdated.focus.rootRecord record firstPresent member identity).trans firstHeaderStored
  have secondIdentity : identify secondMiddle.focus.rootRecord.1 = identify secondCurrent.focus.rootRecord.1 := by
    have roots := congrArg (fun current : Cursor α ρ => identify current.focus.rootRecord) secondRaw
    simpa only [Cursor.mapRecords,Source.mapRecords_root] using roots
  have firstIdentity : identify firstUpdated.focus.rootRecord.1 = identify firstCurrent.focus.rootRecord.1 := by
    have roots := congrArg (fun current : Cursor α ρ => identify current.focus.rootRecord) firstRaw
    simpa only [Cursor.mapRecords,Source.mapRecords_root] using roots
  have refreshedInvariant : SourceRecordPredicate.Holds predicate secondUpdated.tree := by
    apply SourceRecordPredicate.write predicate secondMiddle (PrimaryHeaderRefresh.edit secondHeader secondHeader.rootId secondMiddle.focus.rootRecord)
      (secondAtRoot.1 ▸ middleInvariant)
    intro same
    exact False.elim (distinct (firstIdentity.symm.trans (same.symm.trans secondIdentity)))
  have targetInvariant : SourceRecordPredicate.Holds predicate target.tree := secondFinalRep.1.symm ▸ refreshedInvariant
  have firstIdentityFinal : identify firstReached.focus.rootRecord.1 = identify firstUpdated.focus.rootRecord.1 := by
    have roots := congrArg (fun current : Cursor α ρ => identify current.focus.rootRecord) firstFinalRaw
    simpa only [Cursor.mapRecords,Source.mapRecords_root] using roots
  have firstStored := SourceRecordPredicate.focused predicate firstReached (firstFinalRep.1 ▸ targetInvariant) firstIdentityFinal
  have actual := MultiSourceFinish.finish (fun _ => ()) (fun _ => some RootRecordTour.State.reading)
    (fun _ => PrimaryHeaderRefresh.program second secondHeader secondHeader.rootId []) front back
  exact ⟨target,firstReads++secondReads,firstReached,secondUpdated,actual,secondErases.trans firstErases,
    firstFinalRep,secondFinalRep,firstFinalRaw.trans firstRaw,
    (PrimaryHeaderRefresh.refreshed_erases secondHeader secondHeader.rootId secondMiddle).trans secondRaw,
    firstStored,secondHeaderStored,targetValid⟩

end TangoSquared.Paper20261030.PrimaryHeaderPairRefresh

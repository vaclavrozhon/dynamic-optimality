import ChaCha.Paper20261030.HeadCacheFrame
import ChaCha.Paper20261030.PrimaryHeaderPairRefresh

set_option autoImplicit false

/-! Cache-frame certificates for the actual metadata compiler and the
actual one-root and two-root refresh programs. Determinism identifies
the checked execution with an already obtained endpoint run, so callers
do not need a strengthened runtime controller or extra runtime fingers.
-/

namespace ChaCha.Paper20261030.HeadCacheFrame

open ColoredStorage SourcePointer Structural SourcePositions MultiSourceProgram PrimaryHeaderController

variable {α ρ ι η μ F σ : Type*} [DecidableEq F]

/-- Physical head edits compiled by `MultiSourceAugment` are inert on
the cache field at every immutable physical identifier. -/
theorem augment_frame (identify : ρ → ι) {source : Program σ F ρ} {state last : σ}
    {before after : Configuration F α ρ} {reads cost}
    (run : Run source state before last after reads cost)
    (order : after.tree.inorderLabels identify = before.tree.inorderLabels identify)
    (config : Configuration F α (ρ × μ)) (erases : config.mapRecords Prod.fst = before)
    (unique : (config.tree.inventory (identify ∘ Prod.fst)).Nodup)
    {target : Configuration F α (ρ × μ)} {observed total}
    (actual : Run (MultiSourceAugment.program source) (.ready state) config (.ready last) target observed total) :
    MetadataFrame identify [] config.tree target.tree :=
  MetadataFrame.of_paired identify config.tree target.tree unique
    (MultiSourceAugment.paired_inventory identify run order config erases actual)

theorem refresh_frame (identify : ρ → ι) (header : Header η) (freshId : η)
    (current : Cursor α (Record ρ η))
    (unique : (current.tree.inventory (identify ∘ Prod.fst)).Nodup) :
    MetadataFrame identify [identify current.focus.rootRecord.1] current.tree
      (PrimaryHeaderRefresh.refreshed header freshId current).tree :=
  MetadataFrame.write identify current (some {header with rootId := freshId}) unique

/-- A frame for any actual run of a reached root refresh. -/
theorem refresh_frame_of_run (identify : ρ → ι) (finger : F) (header : Header η) (freshId : η)
    (current : Cursor α (Record ρ η)) (config : Configuration F α (Record ρ η))
    (represented : MultiSourceSingleCursor.Represents finger current config)
    (valid : WellFormed config) (unique : (config.tree.inventory (identify ∘ Prod.fst)).Nodup)
    {target : Configuration F α (Record ρ η)} {reads cost}
    (run : Run (PrimaryHeaderRefresh.program finger header freshId [])
      (some .reading) config (some .done) target reads cost) :
    MetadataFrame identify [identify current.focus.rootRecord.1] config.tree target.tree := by
  obtain ⟨checked,_,actual,_,reached,_⟩ :=
    PrimaryHeaderRefresh.at_cursor finger header freshId current config represented valid
  have same := actual.deterministic run
  rw [← same.2.1,reached.1,represented.1]
  exact refresh_frame identify header freshId current (represented.1 ▸ unique)

/-- The pair refresh changes only the two reached physical roots.
The frame itself does not need their distinctness; distinctness is needed
separately when both prescribed header values are required afterwards. -/
theorem pair_refresh_frame_of_run (identify : ρ → ι) (first second : F)
    (firstHeader secondHeader : Header η)
    (config : Configuration F α (Record ρ η)) (firstCurrent secondCurrent : Cursor α (Record ρ η))
    (firstRep : MultiSourceSingleCursor.Represents first firstCurrent config)
    (secondRep : MultiSourceSingleCursor.Represents second secondCurrent config)
    (valid : WellFormed config) (unique : (config.tree.inventory (identify ∘ Prod.fst)).Nodup)
    {target : Configuration F α (Record ρ η)} {reads cost}
    (run : Run (PrimaryHeaderPairRefresh.program first second firstHeader secondHeader)
      (.first (some .reading)) config (.second () (some .done)) target reads cost) :
    MetadataFrame identify [identify firstCurrent.focus.rootRecord.1,identify secondCurrent.focus.rootRecord.1]
      config.tree target.tree := by
  obtain ⟨middle,firstReads,front,firstErases,_,middleValid⟩ :=
    PrimaryHeaderRefresh.at_cursor first firstHeader firstHeader.rootId firstCurrent config firstRep valid
  have frontFrame := refresh_frame_of_run identify first firstHeader firstHeader.rootId firstCurrent config
    firstRep valid unique front
  have secondInMiddle : MultiSourceSingleCursor.Represents second (secondCurrent.mapRecords Prod.fst)
      (middle.mapRecords Prod.fst) := firstErases.symm ▸ secondRep.mapRecords Prod.fst
  obtain ⟨secondMiddle,secondAtRoot,secondRaw⟩ := MultiSourceSingleCursor.lift_represents Prod.fst second
    (secondCurrent.mapRecords Prod.fst) middle secondInMiddle
  obtain ⟨checked,secondReads,back,_,_,_⟩ :=
    PrimaryHeaderRefresh.at_cursor second secondHeader secondHeader.rootId secondMiddle middle secondAtRoot middleValid
  have middleUnique : (middle.tree.inventory (identify ∘ Prod.fst)).Nodup := frontFrame.ids.symm ▸ unique
  have backFrame := refresh_frame_of_run identify second secondHeader secondHeader.rootId secondMiddle middle
    secondAtRoot middleValid middleUnique back
  have secondId : identify secondMiddle.focus.rootRecord.1 = identify secondCurrent.focus.rootRecord.1 := by
    simpa only [Cursor.mapRecords,Source.mapRecords_root] using
      congrArg (fun current : Cursor α ρ => identify current.focus.rootRecord) secondRaw
  have combined := MultiSourceFinish.finish (fun _ => ()) (fun _ => some RootRecordTour.State.reading)
    (fun _ => PrimaryHeaderRefresh.program second secondHeader secondHeader.rootId []) front back
  have actual : Run (PrimaryHeaderPairRefresh.program first second firstHeader secondHeader)
      (.first (some .reading)) config (.second () (some .done)) checked
      (firstReads++secondReads) (2+2) := combined
  have same := actual.deterministic run
  rw [← same.2.1]
  simpa only [List.singleton_append,secondId] using frontFrame.trans backFrame

end ChaCha.Paper20261030.HeadCacheFrame

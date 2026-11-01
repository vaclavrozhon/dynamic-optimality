import TangoSquared.Paper20261030.CachedAncestorHandoff
import TangoSquared.Paper20261030.CursorAncestorSplit

set_option autoImplicit false

/-! Recovering the cached active component after a reached incoming
component is prepared. An erased proper-descendant context identifies
the actual ancestor. Its retained finger and cache then recover the
canonical active view in the final shared configuration. -/

namespace TangoSquared.Paper20261030.CachedRootOperation

open ColoredStorage SourcePointer Structural PhysicalPacketStaging PacketLayers MultiSourceProgram SourcePositions

variable {α β ρ ι μ F : Type*} [DecidableEq ι] [DecidableEq F]

theorem reached_ancestor (packet : Packet α ρ ι) (old : ι) (target : Source β (Context.Cell α ρ ι))
    (initial final : Configuration F β (Context.Cell α ρ ι × μ))
    (kept : RetainedMetadata Prod.fst target.rootRecord.1 initial.tree final.tree)
    (entry exit anchor : F) (current : Cursor β (Context.Cell α ρ ι))
    (entered : MultiSourceSingleCursor.Represents entry current (initial.mapRecords Prod.fst))
    (parent : Cursor β (Context.Cell α ρ ι × μ))
    (parentRep : MultiSourceSingleCursor.Represents anchor parent initial)
    (insideView : List (Frame β (Packet α ρ ι))) (proper : insideView ≠ [])
    (context : current.ancestors.map (Frame.mapRecords Prod.snd) = insideView ++
      (parent.mapRecords Prod.fst).ancestors.map (Frame.mapRecords Prod.snd))
    (returned : MultiSourceSingleCursor.Represents exit
      (EnclosingPacketOperation.output packet old ⟨target,current.ancestors⟩) (final.mapRecords Prod.fst))
    (unique : ((final.mapRecords Prod.fst).tree.inventory Prod.fst).Nodup)
    (parked : fingerLabel Prod.fst (final.mapRecords Prod.fst) anchor =
      fingerLabel Prod.fst (initial.mapRecords Prod.fst) anchor)
    (view : Source β (Packet α ρ ι))
    (finalView : (final.mapRecords Prod.fst).tree.mapRecords Prod.snd =
      plug view ((parent.mapRecords Prod.fst).ancestors.map (Frame.mapRecords Prod.snd))) :
    ∃ reached : Cursor β (Context.Cell α ρ ι × μ),
      MultiSourceSingleCursor.Represents anchor reached final ∧
      (reached.focus.mapRecords Prod.fst).mapRecords Prod.snd = view ∧
      reached.focus.rootRecord.1.1 = parent.focus.rootRecord.1.1 ∧
      reached.focus.rootRecord.2 = parent.focus.rootRecord.2 ∧
      (reached.mapRecords Prod.fst).ancestors = (parent.mapRecords Prod.fst).ancestors := by
  have parentRaw := parentRep.mapRecords Prod.fst
  obtain ⟨inside,split,innerView,parentFocus⟩ := ancestor_split Prod.snd current (parent.mapRecords Prod.fst)
    (entered.1.symm.trans parentRaw.1) insideView context
  have insideProper : inside ≠ [] := by
    intro empty
    apply proper
    rw [empty,List.map_nil] at innerView
    exact innerView.symm
  have parentId : parent.focus.rootRecord.1.1 = (plug current.focus inside).rootRecord.1 := by
    have identity := congrArg (fun source : Source β (Context.Cell α ρ ι) => source.rootRecord.1) parentFocus
    simpa only [Cursor.mapRecords,Source.mapRecords_root] using identity
  have retainedLabel : fingerLabel Prod.fst (final.mapRecords Prod.fst) anchor = some (plug current.focus inside).rootRecord.1 := by
    rw [parked,fingerLabel_of_represents Prod.fst _ anchor _ parentRaw]
    simpa only [Cursor.mapRecords,Source.mapRecords_root] using congrArg some parentId
  rw [split] at returned
  obtain ⟨reached,located,reachedErases,cache⟩ := ancestor_handoff packet old current.focus target inside
    (parent.mapRecords Prod.fst).ancestors insideProper initial final kept exit anchor parent parentRep parentId
    returned unique retainedLabel
  have reachedId := EnclosingPacketOperation.ancestor_id packet old current.focus target inside
    (parent.mapRecords Prod.fst).ancestors insideProper
  have identity : reached.focus.rootRecord.1.1 = parent.focus.rootRecord.1.1 := by
    have actual := congrArg (fun cursor : Cursor β (Context.Cell α ρ ι) => cursor.focus.rootRecord.1) reachedErases
    simp only [Cursor.mapRecords,Source.mapRecords_root] at actual
    exact actual.trans (reachedId.trans parentId.symm)
  let erased := (reached.mapRecords Prod.fst).mapRecords Prod.snd
  let expected : Cursor β (Packet α ρ ι) :=
    ⟨view,(parent.mapRecords Prod.fst).ancestors.map (Frame.mapRecords Prod.snd)⟩
  have sameTree : erased.tree = expected.tree := by
    rw [Cursor.mapRecords_tree,Cursor.mapRecords_tree,← located.1]
    exact finalView
  have sameAddress : address erased = address expected := by
    change address ((reached.mapRecords Prod.fst).mapRecords Prod.snd) = _
    rw [reachedErases]
    rfl
  have same := eq_of_tree_address erased expected sameTree sameAddress
  have ancestors := congrArg Cursor.ancestors reachedErases
  exact ⟨reached,located,congrArg Cursor.focus same,identity,cache,ancestors⟩

end TangoSquared.Paper20261030.CachedRootOperation

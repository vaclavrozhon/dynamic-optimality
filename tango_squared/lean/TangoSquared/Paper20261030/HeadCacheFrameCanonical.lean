import TangoSquared.Paper20261030.HeadCacheFramePayload
import TangoSquared.Paper20261030.EnclosingPayloadOccurrence
import TangoSquared.Paper20261030.EnclosedRootedComponentExecution

set_option autoImplicit false

/-! A canonical component operation protects every retained real payload
cache. Its actual output assembly supplies the proper payload occurrence;
inorder transport supplies its immutable physical root id. Thus the caller
does not assume either changed-root exclusion or a parked payload finger.
-/

namespace TangoSquared.Paper20261030.HeadCacheFrame

open ColoredStorage SourcePointer Structural SourcePositions PhysicalForestMetadata
open LocalComponentForestCompiler LocalComponentCompiler ForestConnector.ThreeColors MultiSourceProgram
open EnclosedRootedComponentExecution (Packet Cell)

variable {α β ρ ι η μ : Type*} [DecidableEq α]

local instance cacheFrameCanonicalColorOrder : LinearOrder (Option Bool) := inferInstanceAs (LinearOrder (WithBot Bool))

theorem canonical_payload_cache
    (color : α → Option Bool) (decorated : Source α (η × ρ))
    (forest : TaggedForest (Option Bool) α (LocalColoredCompiler.LogicalRecord ρ η (Option Bool)) ι)
    (represented : ProjectionForest.Represents color ⟨annotate Prod.fst color none decorated,[]⟩ (erase forest))
    (headerKey : α) (payload : Option Bool → α → Source β (Packet α ρ ι η))
    (config : Configuration (Option Bool) β (Packet α ρ ι η))
    (assembled : ForestConnector.assemble (representation none wingOrientation headerKey payload forest)
      (layout (representation none wingOrientation headerKey payload forest)) = some config)
    {before after : Source β (Cell α ρ ι η × μ)}
    (parent : Cursor β (Cell α ρ ι η × μ)) (parentTree : parent.tree = after)
    (enclosing : Packet α ρ ι η)
    (parentView : (parent.focus.mapRecords Prod.fst).mapRecords Prod.snd = config.tree.setRoot enclosing)
    (frame : MetadataFrame Prod.fst [parent.focus.rootRecord.1.1] before after)
    (leafWord : before.shape.leaves = after.shape.leaves)
    (order : after.inorderLabels (fun record => record.1.1) = before.inorderLabels (fun record => record.1.1))
    (distinct : before.shape.leaves.Nodup)
    (unique : (after.inventory (fun record => record.1.1)).Nodup)
    (old : Cursor β (Cell α ρ ι η × μ)) (oldTree : old.tree = before)
    (key : α) (member : key ∈ decorated.shape.leaves) (real : color key ≠ none)
    (oldPayload : ((old.focus.mapRecords Prod.fst).mapRecords Prod.snd).setRoot (payload (color key) key).rootRecord =
      payload (color key) key) :
    ∃ actual : Cursor β (Cell α ρ ι η × μ), actual.tree = after ∧
      actual.focus.rootRecord.1.1 = old.focus.rootRecord.1.1 ∧
      old.focus.rootRecord.1.1 ≠ parent.focus.rootRecord.1.1 ∧
      actual.focus.rootRecord.2 = old.focus.rootRecord.2 ∧
      ((actual.focus.mapRecords Prod.fst).mapRecords Prod.snd).setRoot (payload (color key) key).rootRecord =
        payload (color key) key := by
  obtain ⟨routing,_,inside,proper,occurrence⟩ := real_payload_occurs color decorated forest represented
    headerKey payload config assembled key member real
  let focus := (payload (color key) key).setRoot (routing.map some ++ none::(payload (color key) key).rootRecord)
  obtain ⟨changed,changedProper,changedTree⟩ := proper_subtree_setRoot focus inside proper enclosing
  let rawParent := (parent.mapRecords Prod.fst).mapRecords Prod.snd
  have parentFocus : rawParent.focus = plug focus changed := by
    change (parent.focus.mapRecords Prod.fst).mapRecords Prod.snd = _
    rw [parentView,occurrence]
    exact changedTree
  let view : Cursor β (Packet α ρ ι η) := ⟨focus,changed ++ rawParent.ancestors⟩
  have viewTree : view.tree = (after.mapRecords Prod.fst).mapRecords Prod.snd := by
    change plug focus (changed ++ rawParent.ancestors) = _
    rw [plug_append,← parentFocus]
    change rawParent.tree = _
    rw [Cursor.mapRecords_tree,Cursor.mapRecords_tree,parentTree]
  have normalized : view.focus.setRoot (payload (color key) key).rootRecord = payload (color key) key := by
    change ((payload (color key) key).setRoot _).setRoot _ = _
    cases payload (color key) key <;> rfl
  obtain ⟨actual,actualTree,actualErases,identity,excluded,cache,_⟩ := MetadataFrame.retained_proper_payload
    parent.focus.rootRecord.1.1 frame leafWord order distinct unique old oldTree view viewTree
    (payload (color key) key).rootRecord (payload (color key) key).rootRecord
    (oldPayload.trans normalized.symm) parent parentTree rfl changed changedProper parentFocus
  refine ⟨actual,actualTree,identity,excluded,cache,?_⟩
  have focusEq := congrArg Cursor.focus actualErases
  change (actual.focus.mapRecords Prod.fst).mapRecords Prod.snd = view.focus at focusEq
  rw [focusEq]
  exact normalized

end TangoSquared.Paper20261030.HeadCacheFrame

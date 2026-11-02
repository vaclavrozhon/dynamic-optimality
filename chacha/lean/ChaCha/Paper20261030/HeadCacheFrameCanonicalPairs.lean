import ChaCha.Paper20261030.HeadCacheFrameProtection
import ChaCha.Paper20261030.HeadCacheFrameCanonical
import ChaCha.Paper20261030.ComponentProjectionWords

set_option autoImplicit false

/-! Canonical component assemblies discharge the geometry in a two-root
cache frame. Distinct real ports expand to disjoint original-key words;
a real port of a child component lies properly below both component roots.
The certificates are ghost descriptions of actual endpoint occurrences.
-/

namespace ChaCha.Paper20261030.HeadCacheFrame

open ColoredStorage SourcePointer Structural SourcePositions SubtreeMetadata PhysicalForestMetadata
open LocalComponentForestCompiler LocalComponentCompiler ForestConnector.ThreeColors MultiSourceProgram
open EnclosedRootedComponentExecution (Packet Cell)

variable {α β ρ ι η μ : Type*} [DecidableEq α]

local instance canonicalPairsColorOrder : LinearOrder (Option Bool) := inferInstanceAs (LinearOrder (WithBot Bool))

/-- An erased canonical assembly at an actual cached component root. -/
structure CanonicalAt (root : Cursor β (Cell α ρ ι η × μ)) where
  color : α → Option Bool
  decorated : Source α (η × ρ)
  forest : TaggedForest (Option Bool) α (LocalColoredCompiler.LogicalRecord ρ η (Option Bool)) ι
  represented : ProjectionForest.Represents color ⟨annotate Prod.fst color none decorated,[]⟩ (erase forest)
  headerKey : α
  payload : Option Bool → α → Source β (Packet α ρ ι η)
  config : Configuration (Option Bool) β (Packet α ρ ι η)
  assembled : ForestConnector.assemble (representation none wingOrientation headerKey payload forest)
    (layout (representation none wingOrientation headerKey payload forest)) = some config
  enclosing : Packet α ρ ι η
  view : (root.focus.mapRecords Prod.fst).mapRecords Prod.snd = config.tree.setRoot enclosing

theorem CanonicalAt.payload_view {root : Cursor β (Cell α ρ ι η × μ)} (data : CanonicalAt root)
    (key : α) (member : key ∈ data.decorated.shape.leaves) (real : data.color key ≠ none) :
    ∃ view : Cursor β (Packet α ρ ι η),
      view.tree = (root.tree.mapRecords Prod.fst).mapRecords Prod.snd ∧
      view.focus.setRoot (data.payload (data.color key) key).rootRecord = data.payload (data.color key) key ∧
      view.focus.shape.leaves = (data.payload (data.color key) key).shape.leaves ∧
      view.focus.shape.leaves.length < root.focus.shape.leaves.length := by
  obtain ⟨routing,_,inside,proper,occurrence⟩ := real_payload_occurs data.color data.decorated data.forest data.represented
    data.headerKey data.payload data.config data.assembled key member real
  let focus := (data.payload (data.color key) key).setRoot
    (routing.map some ++ none::(data.payload (data.color key) key).rootRecord)
  obtain ⟨changed,changedProper,changedTree⟩ := proper_subtree_setRoot focus inside proper data.enclosing
  let rawRoot := (root.mapRecords Prod.fst).mapRecords Prod.snd
  have parentFocus : rawRoot.focus = plug focus changed := by
    change (root.focus.mapRecords Prod.fst).mapRecords Prod.snd = _
    rw [data.view,occurrence]
    exact changedTree
  let view : Cursor β (Packet α ρ ι η) := ⟨focus,changed ++ rawRoot.ancestors⟩
  refine ⟨view,?_,?_,?_,?_⟩
  · change plug focus (changed ++ rawRoot.ancestors) = _
    rw [plug_append,← parentFocus]
    change rawRoot.tree = _
    rw [Cursor.mapRecords_tree,Cursor.mapRecords_tree]
  · change ((data.payload (data.color key) key).setRoot _).setRoot _ = _
    cases data.payload (data.color key) key <;> rfl
  · exact congrArg RouterProjection.Router.leaves (source_setRoot_shape _ _)
  · have leaves : root.focus.shape.leaves = (plug focus changed).shape.leaves := by
      simpa only [rawRoot,Cursor.mapRecords,Source.mapRecords_shape] using
        congrArg (fun tree => tree.shape.leaves) parentFocus
    rw [leaves]
    exact proper_leaves_lt focus changed changedProper

private theorem flatMap_blocks_disjoint {κ τ : Type*} [DecidableEq κ]
    (keys : List κ) (word : κ → List τ) (distinct : (keys.flatMap word).Nodup)
    (left right : κ) (leftMem : left ∈ keys) (rightMem : right ∈ keys) (different : left ≠ right) :
    List.Disjoint (word left) (word right) := by
  induction keys with
  | nil => simp only [List.not_mem_nil] at leftMem
  | cons key rest ih =>
    have parts := List.nodup_append'.mp distinct
    rcases List.mem_cons.mp leftMem with leftEq | leftRest
    · subst left
      have rightRest : right ∈ rest := (List.mem_cons.mp rightMem).resolve_left (Ne.symm different)
      exact List.disjoint_left.mpr (fun value leftValue rightValue =>
        List.disjoint_left.mp parts.2.2 leftValue (List.mem_flatMap.mpr ⟨right,rightRest,rightValue⟩))
    · rcases List.mem_cons.mp rightMem with rightEq | rightRest
      · subst right
        exact List.disjoint_left.mpr (fun value leftValue rightValue =>
          List.disjoint_left.mp parts.2.2 rightValue (List.mem_flatMap.mpr ⟨left,leftRest,leftValue⟩))
      · exact ih parts.2.1 leftRest rightRest

/-- Different real logical ports of one canonical component have disjoint
original-key payloads, as follows from the actual assembled leaf word. -/
theorem CanonicalAt.payloads_disjoint {root : Cursor β (Cell α ρ ι η × μ)} (data : CanonicalAt root)
    (distinct : root.focus.shape.leaves.Nodup)
    (left right : α) (leftMem : left ∈ data.decorated.shape.leaves) (rightMem : right ∈ data.decorated.shape.leaves)
    (leftReal : data.color left ≠ none) (rightReal : data.color right ≠ none) (different : left ≠ right) :
    List.Disjoint (data.payload (data.color left) left).shape.leaves (data.payload (data.color right) right).shape.leaves := by
  classical
  let physical := representation none wingOrientation data.headerKey data.payload data.forest
  obtain ⟨header,present⟩ := virtual_present (C := Option Bool) none wingOrientation data.headerKey data.payload data.forest
  have same : data.config = ForestConnector.ThreeColors.configuration physical header :=
    Option.some.inj (data.assembled.symm.trans (ForestConnector.ThreeColors.assemble_configuration physical header present))
  have configDistinct : data.config.tree.shape.leaves.Nodup := by
    have leaves := congrArg (fun tree => tree.shape.leaves) data.view
    simp only [Source.mapRecords_shape,source_setRoot_shape] at leaves
    exact leaves ▸ distinct
  rw [same,ForestConnector.ThreeColors.configuration_leaves] at configDistinct
  have leftWord := real_word data.color ⟨data.decorated,[]⟩ data.forest data.represented
    none (some true) (by decide) wingOrientation data.headerKey data.payload
  have rightWord := real_word data.color ⟨data.decorated,[]⟩ data.forest data.represented
    none (some false) (by decide) wingOrientation data.headerKey data.payload
  let keys (side : Bool) := if wingOrientation (some side) then
    (data.decorated.shape.leaves.filter (keepColor data.color (some side))).reverse
    else data.decorated.shape.leaves.filter (keepColor data.color (some side))
  have keyMem (key : α) (mem : key ∈ data.decorated.shape.leaves) (side : Bool) (colorEq : data.color key = some side) :
      key ∈ keys side := by
    have filtered : key ∈ data.decorated.shape.leaves.filter (keepColor data.color (some side)) := by
      simp only [List.mem_filter,keepColor,decide_eq_true_eq]
      exact ⟨mem,colorEq⟩
    dsimp [keys]
    split <;> simp_all only [List.mem_reverse]
  have leftWord' : ForestConnector.ThreeColors.word physical (some true) =
      (keys true).flatMap (fun key => (data.payload (some true) key).shape.leaves) := by
    exact leftWord
  have rightWord' : ForestConnector.ThreeColors.word physical (some false) =
      (keys false).flatMap (fun key => (data.payload (some false) key).shape.leaves) := by
    exact rightWord
  rw [leftWord',rightWord'] at configDistinct
  have outer := List.nodup_append'.mp configDistinct
  have front := List.nodup_append'.mp outer.1
  have cross : List.Disjoint ((keys true).flatMap (fun key => (data.payload (some true) key).shape.leaves))
      ((keys false).flatMap (fun key => (data.payload (some false) key).shape.leaves)) := by
    exact List.disjoint_left.mpr (fun value onLeft onRight =>
      List.disjoint_left.mp outer.2.2 (List.mem_append_left _ onLeft) onRight)
  obtain ⟨leftSide,leftColor⟩ := Option.ne_none_iff_exists'.mp leftReal
  obtain ⟨rightSide,rightColor⟩ := Option.ne_none_iff_exists'.mp rightReal
  have leftKey := keyMem left leftMem leftSide leftColor
  have rightKey := keyMem right rightMem rightSide rightColor
  rw [leftColor,rightColor]
  cases leftSide <;> cases rightSide
  · exact flatMap_blocks_disjoint _ _ outer.2.1 left right leftKey rightKey different
  · exact List.disjoint_left.mpr (fun value leftValue rightValue => List.disjoint_left.mp cross
      (List.mem_flatMap.mpr ⟨right,rightKey,rightValue⟩) (List.mem_flatMap.mpr ⟨left,leftKey,leftValue⟩))
  · exact List.disjoint_left.mpr (fun value leftValue rightValue => List.disjoint_left.mp cross
      (List.mem_flatMap.mpr ⟨left,leftKey,leftValue⟩) (List.mem_flatMap.mpr ⟨right,rightKey,rightValue⟩))
  · exact flatMap_blocks_disjoint _ _ front.1 left right leftKey rightKey different

/-- Two actual final component roots, with the child occupying one real
port of the parent's canonical assembly. -/
structure CanonicalPair (parent child : Cursor β (Cell α ρ ι η × μ)) where
  parentData : CanonicalAt parent
  childData : CanonicalAt child
  boundary : α
  member : boundary ∈ parentData.decorated.shape.leaves
  real : parentData.color boundary ≠ none
  attached : parentData.payload (parentData.color boundary) boundary = childData.config.tree

omit [DecidableEq α] in
theorem cursor_leaves_nodup (current : Cursor α ρ) (distinct : current.tree.shape.leaves.Nodup) :
    current.focus.shape.leaves.Nodup := by
  change (plug current.focus current.ancestors).shape.leaves.Nodup at distinct
  rw [leaves_decomposition] at distinct
  exact (List.nodup_append'.mp (List.nodup_append'.mp distinct).1).2.1

theorem CanonicalAt.leaves {root : Cursor β (Cell α ρ ι η × μ)} (data : CanonicalAt root) :
    root.focus.shape.leaves = data.config.tree.shape.leaves := by
  simpa only [Source.mapRecords_shape,source_setRoot_shape] using
    congrArg (fun tree => tree.shape.leaves) data.view

/-- Every vertex of an unchanged parent payload is protected from both
refreshes. The child root exclusion follows from disjoint canonical ports,
with no independent exclusion or geometric premise. -/
theorem CanonicalPair.protect_parent_payload
    {before after : Source β (Cell α ρ ι η × μ)}
    {parent child : Cursor β (Cell α ρ ι η × μ)} (pair : CanonicalPair parent child)
    (parentTree : parent.tree = after) (childTree : child.tree = after)
    (frame : MetadataFrame Prod.fst [parent.focus.rootRecord.1.1,child.focus.rootRecord.1.1] before after)
    (leafWord : before.shape.leaves = after.shape.leaves)
    (order : after.inorderLabels (fun record => record.1.1) = before.inorderLabels (fun record => record.1.1))
    (distinct : before.shape.leaves.Nodup)
    (unique : (after.inventory (fun record => record.1.1)).Nodup)
    (old : Cursor β (Cell α ρ ι η × μ)) (oldTree : old.tree = before)
    (key : α) (member : key ∈ pair.parentData.decorated.shape.leaves)
    (real : pair.parentData.color key ≠ none) (away : key ≠ pair.boundary)
    (retained : ((old.focus.mapRecords Prod.fst).mapRecords Prod.snd).setRoot
      (pair.parentData.payload (pair.parentData.color key) key).rootRecord =
        pair.parentData.payload (pair.parentData.color key) key) :
    Protects Prod.fst (fun ident => ident ∈ old.focus.inventory (fun record => record.1.1)) before after := by
  obtain ⟨view,viewTree,normalized,viewLeaves,smaller⟩ := pair.parentData.payload_view key member real
  have parentDistinct : parent.focus.shape.leaves.Nodup :=
    cursor_leaves_nodup parent (parentTree.symm ▸ (leafWord ▸ distinct))
  have disjoint := pair.parentData.payloads_disjoint parentDistinct key pair.boundary member pair.member real pair.real away
  have childLeaves : child.focus.shape.leaves =
      (pair.parentData.payload (pair.parentData.color pair.boundary) pair.boundary).shape.leaves := by
    rw [pair.attached]
    exact pair.childData.leaves
  apply MetadataFrame.protect_retained_payload_pair parent child parentTree childTree frame leafWord order distinct unique
    old oldTree view (viewTree.trans (congrArg (fun tree => (tree.mapRecords Prod.fst).mapRecords Prod.snd) parentTree))
    (pair.parentData.payload (pair.parentData.color key) key).rootRecord
    (pair.parentData.payload (pair.parentData.color key) key).rootRecord
    (retained.trans normalized.symm) (Or.inl smaller)
  apply Or.inr
  rw [viewLeaves,childLeaves]
  exact List.disjoint_left.mp disjoint

/-- Every vertex of a child real payload lies strictly below both final
refreshed roots. Its cache therefore survives the two-component phase. -/
theorem CanonicalPair.protect_child_payload
    {before after : Source β (Cell α ρ ι η × μ)}
    {parent child : Cursor β (Cell α ρ ι η × μ)} (pair : CanonicalPair parent child)
    (parentTree : parent.tree = after) (childTree : child.tree = after)
    (frame : MetadataFrame Prod.fst [parent.focus.rootRecord.1.1,child.focus.rootRecord.1.1] before after)
    (leafWord : before.shape.leaves = after.shape.leaves)
    (order : after.inorderLabels (fun record => record.1.1) = before.inorderLabels (fun record => record.1.1))
    (distinct : before.shape.leaves.Nodup)
    (unique : (after.inventory (fun record => record.1.1)).Nodup)
    (old : Cursor β (Cell α ρ ι η × μ)) (oldTree : old.tree = before)
    (key : α) (member : key ∈ pair.childData.decorated.shape.leaves)
    (real : pair.childData.color key ≠ none)
    (retained : ((old.focus.mapRecords Prod.fst).mapRecords Prod.snd).setRoot
      (pair.childData.payload (pair.childData.color key) key).rootRecord =
        pair.childData.payload (pair.childData.color key) key) :
    Protects Prod.fst (fun ident => ident ∈ old.focus.inventory (fun record => record.1.1)) before after := by
  obtain ⟨view,viewTree,normalized,_,smaller⟩ := pair.childData.payload_view key member real
  obtain ⟨boundaryView,_,_,boundaryLeaves,boundarySmaller⟩ :=
    pair.parentData.payload_view pair.boundary pair.member pair.real
  have childSmaller : child.focus.shape.leaves.length < parent.focus.shape.leaves.length := by
    rw [boundaryLeaves,pair.attached,← pair.childData.leaves] at boundarySmaller
    exact boundarySmaller
  exact MetadataFrame.protect_retained_payload_pair parent child parentTree childTree frame leafWord order distinct unique
    old oldTree view (viewTree.trans (congrArg (fun tree => (tree.mapRecords Prod.fst).mapRecords Prod.snd) childTree))
    (pair.childData.payload (pair.childData.color key) key).rootRecord
    (pair.childData.payload (pair.childData.color key) key).rootRecord
    (retained.trans normalized.symm) (Or.inl (Nat.lt_trans smaller childSmaller)) (Or.inl smaller)

end ChaCha.Paper20261030.HeadCacheFrame

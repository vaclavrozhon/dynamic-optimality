import ChaCha.Paper20261030.SplayAuxiliarySourceRotations

/-!
# Physical rotations depend only on the original-key source shape

All source records are free bookkeeping in the chosen BST model. A
rotation of the full leaf shape is exactly one ordinary rotation of its
gap encoding, even when records are changed. Restricting or substituting
leaf payloads never increases this one-rotation bound.
-/

namespace ChaCha.Paper20261030.SplayAuxiliary

open DynamicOptimality (RawTree)
open DynamicOptimality.SearchRotation
open ColoredStorage RouterProjection

variable {α β ρ κ : Type*}

theorem source_shape_gaps {a : Source α ρ} {b : Source α κ} (shape : a.shape = b.shape) :
    GapBST.gaps a = GapBST.gaps b ∧ GapBST.lastKey a = GapBST.lastKey b := by
  induction a generalizing b with
  | leaf label record =>
      cases b with
      | leaf other value => cases Router.leaf.inj shape; exact ⟨rfl,rfl⟩
      | fork => cases shape
  | fork record l r ihl ihr =>
      cases b with
      | leaf => cases shape
      | fork value left right =>
          obtain ⟨leftShape,rightShape⟩ := Router.fork.inj shape
          obtain ⟨leftTree,leftLast⟩ := ihl leftShape
          obtain ⟨rightTree,rightLast⟩ := ihr rightShape
          simp only [GapBST.gaps,GapBST.lastKey,leftTree,leftLast,rightTree,rightLast,and_self]

theorem source_shape_encode {a : Source α ρ} {b : Source α κ} (shape : a.shape = b.shape) :
    GapBST.encode a = GapBST.encode b := by
  obtain ⟨tree,last⟩ := source_shape_gaps shape
  simp only [GapBST.encode,tree,last]

theorem source_router_rotation {before after : Router α} (step : Paper20261030.Router.Rotation before after)
    (source : Source α ρ) (shape : source.shape = before) :
    ∃ target : Source α ρ, SourceRotation source target ∧ target.shape = after := by
  induction step generalizing source with
  | root a b c =>
      cases source with
      | leaf => cases shape
      | fork record left right =>
          cases left with
          | leaf => cases shape
          | fork value first second =>
              simp only [Source.shape,Router.fork.injEq] at shape
              rcases shape with ⟨⟨rfl,rfl⟩,rfl⟩
              exact ⟨_,.right first second right value record,rfl⟩
  | rootRev a b c =>
      cases source with
      | leaf => cases shape
      | fork record left right =>
          cases right with
          | leaf => cases shape
          | fork value first second =>
              simp only [Source.shape,Router.fork.injEq] at shape
              rcases shape with ⟨rfl,⟨rfl,rfl⟩⟩
              exact ⟨_,.left left first second record value,rfl⟩
  | left right step ih =>
      cases source with
      | leaf => cases shape
      | fork record l r =>
          obtain ⟨leftShape,rightShape⟩ := Router.fork.inj shape
          obtain ⟨next,move,same⟩ := ih l leftShape
          refine ⟨_,.inLeft move record r,?_⟩
          simp only [Source.shape,same,rightShape]
  | right left step ih =>
      cases source with
      | leaf => cases shape
      | fork record l r =>
          obtain ⟨leftShape,rightShape⟩ := Router.fork.inj shape
          obtain ⟨next,move,same⟩ := ih r rightShape
          refine ⟨_,.inRight l record move,?_⟩
          simp only [Source.shape,same,leftShape]

theorem router_rotation_gaps {a : Source α ρ} {b : Source α κ}
    (step : Paper20261030.Router.Rotation a.shape b.shape) :
    Rotation (GapBST.gaps a) (GapBST.gaps b) ∧ GapBST.lastKey a = GapBST.lastKey b := by
  obtain ⟨target,actual,shape⟩ := source_router_rotation step a rfl
  obtain ⟨tree,last⟩ := source_shape_gaps shape
  exact ⟨tree ▸ actual.gaps,actual.lastKey.trans last⟩

theorem router_rotation_encoded {a : Source α ρ} {b : Source α κ}
    (step : Paper20261030.Router.Rotation a.shape b.shape) :
    Rotation (GapBST.encode a) (GapBST.encode b) := by
  obtain ⟨target,actual,shape⟩ := source_router_rotation step a rfl
  exact source_shape_encode shape ▸ actual.encoded

theorem router_step_encoded {a : Source α ρ} {b : Source α κ}
    (step : Paper20261030.Router.Step a.shape b.shape) :
    ∃ count, Rotations (GapBST.encode a) (GapBST.encode b) count ∧ count ≤ 1 := by
  rcases step with same | rotation
  · exact ⟨0,source_shape_encode same ▸ .refl _,by decide⟩
  · exact ⟨1,.step (router_rotation_encoded rotation) (.refl _),le_rfl⟩

/-- Substitute entire opaque physical payloads for retained leaves, with
ordinary empty-branch suppression. -/
def routerSubstitute (payload : α → Router β) : Router α → Router β
  | .empty => .empty
  | .leaf label => payload label
  | .fork l r => (routerSubstitute payload l).join (routerSubstitute payload r)

theorem router_substitute_rotation (payload : α → Router β) {before after : Router α}
    (step : Paper20261030.Router.Rotation before after) :
    Paper20261030.Router.Step (routerSubstitute payload before) (routerSubstitute payload after) := by
  induction step with
  | root a b c => exact Paper20261030.Router.step_join_assoc _ _ _
  | rootRev a b c => exact Paper20261030.Router.step_join_assoc_rev _ _ _
  | left right step ih => exact Paper20261030.Router.step_join_left ih _
  | right left step ih => exact Paper20261030.Router.step_join_right _ ih

theorem router_substitute_step (payload : α → Router β) {before after : Router α}
    (step : Paper20261030.Router.Step before after) :
    Paper20261030.Router.Step (routerSubstitute payload before) (routerSubstitute payload after) := by
  rcases step with rfl | rotation
  · exact Or.inl rfl
  · exact router_substitute_rotation payload rotation

/-- A colored restriction followed by arbitrary opaque payload attachment
needs at most one rotation for each source rotation. -/
theorem restricted_payload_step (keep : α → Bool) (payload : α → Router β)
    {before after : Source α ρ} (step : SourceRotation before after) :
    Paper20261030.Router.Step
      (routerSubstitute payload (before.shape.prune keep))
      (routerSubstitute payload (after.shape.prune keep)) :=
  router_substitute_step payload (Paper20261030.Router.prune_rotation keep step.router)

end ChaCha.Paper20261030.SplayAuxiliary

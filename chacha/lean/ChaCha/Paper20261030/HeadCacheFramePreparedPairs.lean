import ChaCha.Paper20261030.HeadCacheFrameCanonicalPairs

set_option autoImplicit false

/-! Output companions for pair preparation. The execution endpoint's two
actual final roots and canonical assemblies protect all original retained
payload vertices. The parent payload changes only at the child boundary;
the child's real payloads are unchanged. These statements introduce no
runtime cursors and no assumption about excluded physical identifiers.
-/

namespace ChaCha.Paper20261030.HeadCacheFrame

open ColoredStorage SourcePointer Structural
open EnclosedRootedComponentExecution (Packet Cell)

variable {α β ρ ι η μ : Type*} [DecidableEq α]

/-- Physical ids in an old real payload from a specified port family.
The occurrence is ghost evidence in the shared input tree. -/
def PayloadFamilyIds (before : Source β (Cell α ρ ι η × μ)) (keys : List α)
    (color : α → Option Bool) (payload : Option Bool → α → Source β (Packet α ρ ι η))
    (keep : α → Prop) (ident : ι) : Prop :=
  ∃ key, key ∈ keys ∧ color key ≠ none ∧ keep key ∧
    ∃ old : Cursor β (Cell α ρ ι η × μ), old.tree = before ∧
      ((old.focus.mapRecords Prod.fst).mapRecords Prod.snd).setRoot (payload (color key) key).rootRecord =
        payload (color key) key ∧ ident ∈ old.focus.inventory (fun record => record.1.1)

/-- Both preparation phases protect the union of old parent ports away
from the boundary and all real incoming-child ports. Its premises are
exact output data of the checked pair preparation endpoints. -/
theorem CanonicalPair.protect_prepared_pair
    {before after : Source β (Cell α ρ ι η × μ)}
    {parent child : Cursor β (Cell α ρ ι η × μ)} (pair : CanonicalPair parent child)
    (parentTree : parent.tree = after) (childTree : child.tree = after)
    (frame : MetadataFrame Prod.fst [parent.focus.rootRecord.1.1,child.focus.rootRecord.1.1] before after)
    (leafWord : before.shape.leaves = after.shape.leaves)
    (order : after.inorderLabels (fun record => record.1.1) = before.inorderLabels (fun record => record.1.1))
    (distinct : before.shape.leaves.Nodup)
    (unique : (after.inventory (fun record => record.1.1)).Nodup)
    (parentKeys childKeys : List α)
    (parentLeaves : pair.parentData.decorated.shape.leaves = parentKeys)
    (childLeaves : pair.childData.decorated.shape.leaves = childKeys)
    (parentPayload childPayload : Option Bool → α → Source β (Packet α ρ ι η))
    (parentPayloadEq : pair.parentData.payload = Function.update parentPayload (pair.parentData.color pair.boundary)
      (Function.update (parentPayload (pair.parentData.color pair.boundary)) pair.boundary pair.childData.config.tree))
    (childPayloadEq : pair.childData.payload = childPayload) :
    Protects Prod.fst (fun ident =>
      PayloadFamilyIds before parentKeys pair.parentData.color parentPayload (fun key => key ≠ pair.boundary) ident ∨
      PayloadFamilyIds before childKeys pair.childData.color childPayload (fun _ => True) ident) before after := by
  refine ⟨frame.ids,?_⟩
  intro old oldPresent guarded fresh freshPresent same
  rcases guarded with onParent | onChild
  · obtain ⟨key,member,real,away,payloadOld,payloadOldTree,retained,inside⟩ := onParent
    have payloadEq : pair.parentData.payload (pair.parentData.color key) key = parentPayload (pair.parentData.color key) key := by
      rw [parentPayloadEq]
      by_cases colors : pair.parentData.color key = pair.parentData.color pair.boundary
      · simp only [colors,Function.update_self,Function.update_of_ne away]
      · simp only [Function.update_of_ne colors]
    have protection := pair.protect_parent_payload parentTree childTree frame leafWord order distinct unique
      payloadOld payloadOldTree key (parentLeaves ▸ member) real away (by simpa only [payloadEq] using retained)
    exact protection.retained old oldPresent inside fresh freshPresent same
  · obtain ⟨key,member,real,_,payloadOld,payloadOldTree,retained,inside⟩ := onChild
    have protection := pair.protect_child_payload parentTree childTree frame leafWord order distinct unique
      payloadOld payloadOldTree key (childLeaves ▸ member) real (by simpa only [childPayloadEq] using retained)
    exact protection.retained old oldPresent inside fresh freshPresent same

end ChaCha.Paper20261030.HeadCacheFrame

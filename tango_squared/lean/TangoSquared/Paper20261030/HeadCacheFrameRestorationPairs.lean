import TangoSquared.Paper20261030.HeadCacheFramePreparedPairs

set_option autoImplicit false

/-! Balanced restoration emits the same nested pair certificate as
preparation, with its two refreshed roots listed in the opposite order.
This companion discharges the retained payload cache frame from the actual
final canonical pair and the endpoint's exact two-root metadata frame.
-/

namespace TangoSquared.Paper20261030.HeadCacheFrame

open ColoredStorage SourcePointer Structural
open EnclosedRootedComponentExecution (Packet Cell)

variable {α β ρ ι η μ : Type*} [DecidableEq α]

theorem CanonicalPair.protect_restored_pair
    {before after : Source β (Cell α ρ ι η × μ)}
    {parent child : Cursor β (Cell α ρ ι η × μ)} (pair : CanonicalPair parent child)
    (parentTree : parent.tree = after) (childTree : child.tree = after)
    (frame : MetadataFrame Prod.fst [child.focus.rootRecord.1.1,parent.focus.rootRecord.1.1] before after)
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
  have reordered : MetadataFrame Prod.fst [parent.focus.rootRecord.1.1,child.focus.rootRecord.1.1] before after :=
    frame.mono (by
      intro ident member
      simp only [List.mem_cons,List.not_mem_nil,or_false] at member ⊢
      exact member.elim Or.inr Or.inl)
  exact pair.protect_prepared_pair parentTree childTree reordered leafWord order distinct unique parentKeys childKeys
    parentLeaves childLeaves parentPayload childPayload parentPayloadEq childPayloadEq

end TangoSquared.Paper20261030.HeadCacheFrame

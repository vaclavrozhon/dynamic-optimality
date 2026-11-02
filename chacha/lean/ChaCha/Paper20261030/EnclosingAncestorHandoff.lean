import ChaCha.Paper20261030.EnclosingPacketExtension
import ChaCha.Paper20261030.EnclosingPacketAnchors

set_option autoImplicit false

/-! Returning to a parked proper ancestor after a nested component
operation. The ancestor's immutable identifier is unchanged even when its
own child-reference packet is repaired. Distinct physical ids separate
it from the new nested root, so refreshing the nested cache cannot alter
the ancestor's cache. This module derives the actual reached ancestor
from its retained finger label, with no pointer search. -/

namespace ChaCha.Paper20261030.SourcePositions

open ColoredStorage SourcePointer Structural

variable {α ρ ι : Type*}

theorem proper_ancestor_id_ne (identify : ρ → ι) (focus : Source α ρ)
    (inside outside : List (Frame α ρ)) (proper : inside ≠ [])
    (unique : ((plug focus (inside++outside)).inventory identify).Nodup) :
    identify focus.rootRecord ≠ identify (plug focus inside).rootRecord := by
  intro sameId
  let child : Cursor α ρ := ⟨focus,inside++outside⟩
  let parent : Cursor α ρ := ⟨plug focus inside,outside⟩
  have sameTree : child.tree = parent.tree := plug_append focus inside outside
  have equal := cursors_eq_of_label identify child parent sameTree unique sameId
  have sameSize := congrArg (fun current : Cursor α ρ => current.focus.shape.leaves.length) equal
  have less := SubtreeMetadata.proper_leaves_lt focus inside proper
  change focus.shape.leaves.length = (plug focus inside).shape.leaves.length at sameSize
  omega

end ChaCha.Paper20261030.SourcePositions

namespace ChaCha.Paper20261030.EnclosingPacketOperation

open ColoredStorage SourcePointer Structural PhysicalPacketStaging PacketLayers MultiSourceProgram SourcePositions

variable {α β ρ ι F : Type*} [DecidableEq ι] [DecidableEq F]

private theorem plug_root (before after : Source β (Context.Cell α ρ ι))
    (outside : List (Frame β (Context.Cell α ρ ι))) (proper : outside ≠ []) :
    (plug before outside).rootRecord = (plug after outside).rootRecord := by
  induction outside generalizing before after with
  | nil => exact False.elim (proper rfl)
  | cons first rest ih =>
    cases rest with
    | nil => cases first <;> rfl
    | cons second rest => cases first with
      | left record sibling => exact ih (.fork record before sibling) (.fork record after sibling) (by simp)
      | right sibling record => exact ih (.fork record sibling before) (.fork record sibling after) (by simp)

def ancestor (packet : Packet α ρ ι) (old : ι) (target : Source β (Context.Cell α ρ ι))
    (inside outside : List (Frame β (Context.Cell α ρ ι))) : Cursor β (Context.Cell α ρ ι) :=
  ⟨(output packet old ⟨target,inside⟩).tree,outside⟩

theorem ancestor_tree (packet : Packet α ρ ι) (old : ι) (target : Source β (Context.Cell α ρ ι))
    (inside outside : List (Frame β (Context.Cell α ρ ι))) (proper : inside ≠ []) :
    (ancestor packet old target inside outside).tree = (output packet old ⟨target,inside++outside⟩).tree := by
  rw [extend packet old target inside outside (Or.inl proper)]
  exact (plug_append _ _ _).symm

theorem ancestor_id (packet : Packet α ρ ι) (old : ι) (before after : Source β (Context.Cell α ρ ι))
    (inside outside : List (Frame β (Context.Cell α ρ ι))) (proper : inside ≠ []) :
    (ancestor packet old after inside outside).focus.rootRecord.1 = (plug before inside).rootRecord.1 := by
  have labels := identifier_tree packet old ⟨after,inside⟩
  have roots := congrArg Source.rootRecord labels
  simp only [Source.mapRecords_root] at roots
  exact roots.trans (congrArg Prod.fst (plug_root after before inside proper))

theorem ancestor_different (packet : Packet α ρ ι) (old : ι) (target : Source β (Context.Cell α ρ ι))
    (inside outside : List (Frame β (Context.Cell α ρ ι))) (proper : inside ≠ [])
    (unique : ((output packet old ⟨target,inside++outside⟩).tree.inventory Prod.fst).Nodup) :
    target.rootRecord.1 ≠ (ancestor packet old target inside outside).focus.rootRecord.1 := by
  let repaired := output packet old ⟨target,inside⟩
  have nonempty : repaired.ancestors ≠ [] := by
    cases found : inside with
    | nil => exact False.elim (proper found)
    | cons first rest => simp only [repaired,output,found,List.cons_ne_self,ne_eq,reduceCtorEq,not_false_eq_true]
  rw [extend packet old target inside outside (Or.inl proper)] at unique
  have different := proper_ancestor_id_ne Prod.fst repaired.focus repaired.ancestors outside nonempty unique
  simpa only [repaired,output,PacketPrefixTransfer.output_root_id,ancestor,Cursor.tree] using different

theorem ancestor_handoff (packet : Packet α ρ ι) (old : ι) (before after : Source β (Context.Cell α ρ ι))
    (inside outside : List (Frame β (Context.Cell α ρ ι))) (proper : inside ≠ [])
    (config : Configuration F β (Context.Cell α ρ ι)) (exit finger : F)
    (returned : MultiSourceSingleCursor.Represents exit (output packet old ⟨after,inside++outside⟩) config)
    (unique : (config.tree.inventory Prod.fst).Nodup)
    (parked : fingerLabel Prod.fst config finger = some (plug before inside).rootRecord.1) :
    MultiSourceSingleCursor.Represents finger (ancestor packet old after inside outside) config ∧
      (ancestor packet old after inside outside).focus.rootRecord.1 = (plug before inside).rootRecord.1 ∧
      after.rootRecord.1 ≠ (ancestor packet old after inside outside).focus.rootRecord.1 := by
  have identity := ancestor_id packet old before after inside outside proper
  refine ⟨?_,identity,ancestor_different packet old after inside outside proper (returned.1 ▸ unique)⟩
  apply represents_of_fingerLabel Prod.fst config finger (ancestor packet old after inside outside)
    ((ancestor_tree packet old after inside outside proper).trans returned.1.symm) unique
  rw [identity]
  exact parked

end ChaCha.Paper20261030.EnclosingPacketOperation

import TangoSquared.Paper20261030.SourceSubtreeMetadata
import TangoSquared.Paper20261030.MultiSourceValidity

set_option autoImplicit false

/-! A retained payload is reached by its parked physical finger after a
component operation. The premise describes the payload in the erased
output representation, allowing its enclosing root packet to change.
Exact inorder ids recover the entire payload metadata and identify the
parked finger with this output cursor. No uncharged search is performed. -/

namespace TangoSquared.Paper20261030.SubtreeMetadata

open ColoredStorage SourcePointer

variable {α ρ ι : Type*}

def replacePayload (current : Cursor α (ι × ρ)) (fresh : ρ) : Cursor α (ι × ρ) :=
  ⟨current.focus.setRoot (current.focus.rootRecord.1,fresh),current.ancestors⟩

private theorem root_set (tree : Source α (ι × ρ)) (fresh : ι × ρ) :
    (tree.setRoot fresh).rootRecord = fresh := by cases tree <;> rfl

theorem replacePayload_leaves (current : Cursor α (ι × ρ)) (fresh : ρ) :
    (replacePayload current fresh).tree.shape.leaves = current.tree.shape.leaves :=
  (SourcePointer.Step.write current.focus (current.focus.rootRecord.1,fresh) current.ancestors).leaves.symm

theorem replacePayload_order (current : Cursor α (ι × ρ)) (fresh : ρ) :
    (replacePayload current fresh).tree.inorderLabels Prod.fst = current.tree.inorderLabels Prod.fst :=
  plug_inorderLabels_congr Prod.fst
    (Source.inorderLabels_setRoot Prod.fst current.focus (current.focus.rootRecord.1,fresh) rfl) current.ancestors

theorem focus_replacePayload_eq (before after : Cursor α (ι × ρ)) (old fresh : ρ)
    (whole : before.tree.shape.leaves = after.tree.shape.leaves)
    (distinct : before.tree.shape.leaves.Nodup)
    (erases : (before.focus.mapRecords Prod.snd).setRoot old = (after.focus.mapRecords Prod.snd).setRoot fresh)
    (order : before.tree.inorderLabels Prod.fst = after.tree.inorderLabels Prod.fst) :
    (replacePayload before old).focus = (replacePayload after fresh).focus := by
  apply focus_eq Prod.snd Prod.fst (fun _ _ equality => Prod.ext (congrArg Prod.snd equality) (congrArg Prod.fst equality))
    (replacePayload before old) (replacePayload after fresh)
  · rw [replacePayload_leaves,replacePayload_leaves]
    exact whole
  · rw [replacePayload_leaves]
    exact distinct
  · simpa only [replacePayload,Source.mapRecords_setRoot] using erases
  · rw [replacePayload_order,replacePayload_order]
    exact order

end TangoSquared.Paper20261030.SubtreeMetadata

namespace TangoSquared.Paper20261030.MultiSourceProgram

open ColoredStorage SourcePointer SourcePositions SubtreeMetadata

variable {α ρ ι F σ : Type*} [DecidableEq F]

theorem retained_subtree_handoff_of_leaves
    {before after : Configuration F α (ι × ρ)}
    (leafWord : before.tree.shape.leaves = after.tree.shape.leaves)
    (order : after.tree.inorderLabels Prod.fst = before.tree.inorderLabels Prod.fst)
    (distinct : before.tree.shape.leaves.Nodup) (unique : (after.tree.inventory Prod.fst).Nodup)
    (finger : F) (parked : fingerLabel Prod.fst after finger = fingerLabel Prod.fst before finger)
    (current : Cursor α (ι × ρ)) (positioned : MultiSourceSingleCursor.Represents finger current before)
    (view : Cursor α ρ) (viewTree : view.tree = after.tree.mapRecords Prod.snd)
    (old fresh : ρ)
    (retained : (current.focus.mapRecords Prod.snd).setRoot old = view.focus.setRoot fresh) :
    ∃ actual : Cursor α (ι × ρ),
      MultiSourceSingleCursor.Represents finger actual after ∧ actual.mapRecords Prod.snd = view ∧
      (replacePayload current old).focus = (replacePayload actual fresh).focus := by
  have located : locate (after.tree.mapRecords Prod.snd) (address view) = some view := by
    rw [← viewTree]
    exact locate_cursor view
  obtain ⟨actual,found,erases⟩ := lift_locate Prod.snd after.tree (address view) view located
  have actualTree := locate_tree found
  have whole : current.tree.shape.leaves = actual.tree.shape.leaves := by
    rw [← positioned.1,actualTree]
    exact leafWord
  have focusSame : (current.focus.mapRecords Prod.snd).setRoot old =
      (actual.focus.mapRecords Prod.snd).setRoot fresh := by
    rw [← erases] at retained
    exact retained
  have equal := focus_replacePayload_eq current actual old fresh whole (positioned.1 ▸ distinct) focusSame
    (by rw [← positioned.1,actualTree]; exact order.symm)
  have rootIds : current.focus.rootRecord.1 = actual.focus.rootRecord.1 := by
    have roots := congrArg (fun tree : Source α (ι × ρ) => tree.rootRecord.1) equal
    simpa only [replacePayload,root_set] using roots
  refine ⟨actual,?_,erases,equal⟩
  apply represents_of_fingerLabel Prod.fst after finger actual actualTree unique
  rw [parked,fingerLabel_of_represents Prod.fst before finger current positioned,rootIds]

theorem retained_subtree_handoff {source : Program σ F (ι × ρ)} {state last : σ}
    {before after : Configuration F α (ι × ρ)} {reads cost}
    (run : Run source state before last after reads cost)
    (order : after.tree.inorderLabels Prod.fst = before.tree.inorderLabels Prod.fst)
    (distinct : before.tree.shape.leaves.Nodup) (unique : (after.tree.inventory Prod.fst).Nodup)
    (finger : F) (parked : fingerLabel Prod.fst after finger = fingerLabel Prod.fst before finger)
    (current : Cursor α (ι × ρ)) (positioned : MultiSourceSingleCursor.Represents finger current before)
    (view : Cursor α ρ) (viewTree : view.tree = after.tree.mapRecords Prod.snd)
    (old fresh : ρ)
    (retained : (current.focus.mapRecords Prod.snd).setRoot old = view.focus.setRoot fresh) :
    ∃ actual : Cursor α (ι × ρ),
      MultiSourceSingleCursor.Represents finger actual after ∧ actual.mapRecords Prod.snd = view ∧
      (replacePayload current old).focus = (replacePayload actual fresh).focus :=
  retained_subtree_handoff_of_leaves run.leaves order distinct unique finger parked current positioned view viewTree old fresh retained

end TangoSquared.Paper20261030.MultiSourceProgram

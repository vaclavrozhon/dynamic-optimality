import ChaCha.Paper20261030.SourceInorderLabels
import ChaCha.Paper20261030.SourceIdentifierPositions

set_option autoImplicit false

/-! Recovering the immutable metadata of a retained payload subtree.
With distinct original-key leaves, an unchanged payload occupies the
same inorder interval before and after a component rearrangement. Exact
inorder-label preservation therefore preserves every metadata value in
that payload, including the physical identifier at its root. -/

namespace ChaCha.Paper20261030.SubtreeMetadata

open ColoredStorage SourcePointer

variable {α ρ τ ι : Type*}

def labelsBefore (label : ρ → ι) : List (Frame α ρ) → List ι
  | [] => []
  | .left _ _ :: rest => labelsBefore label rest
  | .right sibling record :: rest => labelsBefore label rest ++ sibling.inorderLabels label ++ [label record]

def labelsAfter (label : ρ → ι) : List (Frame α ρ) → List ι
  | [] => []
  | .left record sibling :: rest => label record :: sibling.inorderLabels label ++ labelsAfter label rest
  | .right _ _ :: rest => labelsAfter label rest

def leavesBefore : List (Frame α ρ) → List α
  | [] => []
  | .left _ _ :: rest => leavesBefore rest
  | .right sibling _ :: rest => leavesBefore rest ++ sibling.shape.leaves

def leavesAfter : List (Frame α ρ) → List α
  | [] => []
  | .left _ sibling :: rest => sibling.shape.leaves ++ leavesAfter rest
  | .right _ _ :: rest => leavesAfter rest

theorem labels_decomposition (label : ρ → ι) (focus : Source α ρ) (outside : List (Frame α ρ)) :
    (plug focus outside).inorderLabels label =
      labelsBefore label outside ++ focus.inorderLabels label ++ labelsAfter label outside := by
  induction outside generalizing focus with
  | nil => simp [labelsBefore,labelsAfter,plug]
  | cons frame rest ih =>
    cases frame <;> simp only [plug,ih,labelsBefore,labelsAfter,Source.inorderLabels,
      List.append_assoc,List.cons_append,List.nil_append]

theorem leaves_decomposition (focus : Source α ρ) (outside : List (Frame α ρ)) :
    (plug focus outside).shape.leaves = leavesBefore outside ++ focus.shape.leaves ++ leavesAfter outside := by
  induction outside generalizing focus with
  | nil => simp [leavesBefore,leavesAfter,plug]
  | cons frame rest ih =>
    cases frame <;> simp only [plug,ih,leavesBefore,leavesAfter,Source.shape,RouterProjection.Router.leaves,List.append_assoc]

theorem labelsBefore_length (label : ρ → ι) (outside : List (Frame α ρ)) :
    (labelsBefore label outside).length = 2 * (leavesBefore outside).length := by
  induction outside with
  | nil => rfl
  | cons frame rest ih => cases frame with
    | left => exact ih
    | right sibling record =>
      have length := sibling.inorderLabels_length label
      simp only [labelsBefore,leavesBefore,List.length_append,List.length_singleton]
      omega

theorem leaves_le_plug (focus : Source α ρ) (outside : List (Frame α ρ)) :
    focus.shape.leaves.length ≤ (plug focus outside).shape.leaves.length := by
  rw [leaves_decomposition]
  simp only [List.length_append]
  omega

theorem proper_leaves_lt (focus : Source α ρ) (outside : List (Frame α ρ)) (proper : outside ≠ []) :
    focus.shape.leaves.length < (plug focus outside).shape.leaves.length := by
  cases outside with
  | nil => exact False.elim (proper rfl)
  | cons first rest =>
    cases first with
    | left record sibling =>
      have positive := sibling.inorderLabels_length (fun _ => ())
      have larger := leaves_le_plug (.fork record focus sibling) rest
      simp only [Source.shape,RouterProjection.Router.leaves,List.length_append] at larger
      change _ < (plug (.fork record focus sibling) rest).shape.leaves.length
      omega
    | right sibling record =>
      have positive := sibling.inorderLabels_length (fun _ => ())
      have larger := leaves_le_plug (.fork record sibling focus) rest
      simp only [Source.shape,RouterProjection.Router.leaves,List.length_append] at larger
      change _ < (plug (.fork record sibling focus) rest).shape.leaves.length
      omega

theorem leavesBefore_eq (before after : Cursor α ρ)
    (whole : before.tree.shape.leaves = after.tree.shape.leaves)
    (distinct : before.tree.shape.leaves.Nodup)
    (focus : before.focus.shape.leaves = after.focus.shape.leaves) :
    leavesBefore before.ancestors = leavesBefore after.ancestors := by
  have oldWord := leaves_decomposition before.focus before.ancestors
  have newWord := leaves_decomposition after.focus after.ancestors
  change before.tree.shape.leaves = _ at oldWord
  change after.tree.shape.leaves = _ at newWord
  have nonempty : before.focus.shape.leaves ≠ [] := by
    have length := before.focus.inorderLabels_length (fun _ => ())
    intro empty
    rw [empty,List.length_nil] at length
    omega
  cases word : before.focus.shape.leaves with
  | nil => exact False.elim (nonempty word)
  | cons key tail =>
    have fresh : after.focus.shape.leaves = key::tail := focus.symm.trans word
    rw [word,List.append_assoc,List.cons_append] at oldWord
    rw [fresh,List.append_assoc,List.cons_append] at newWord
    have unique : (leavesBefore before.ancestors ++ key :: (tail ++ leavesAfter before.ancestors)).Nodup :=
      oldWord ▸ distinct
    obtain ⟨_,uniqueTail,separate⟩ := List.nodup_append.mp unique
    have notBefore : key ∉ leavesBefore before.ancestors :=
      fun member => separate key member key (by simp) rfl
    have notAfter : key ∉ tail ++ leavesAfter before.ancestors := (List.nodup_cons.mp uniqueTail).1
    exact ((List.append_cons_inj_of_notMem notBefore notAfter).mp
      (oldWord.symm.trans (whole.trans newWord))).1

theorem focus_order (label : ρ → ι) (before after : Cursor α ρ)
    (whole : before.tree.shape.leaves = after.tree.shape.leaves)
    (distinct : before.tree.shape.leaves.Nodup)
    (leaves : before.focus.shape.leaves = after.focus.shape.leaves)
    (order : before.tree.inorderLabels label = after.tree.inorderLabels label) :
    before.focus.inorderLabels label = after.focus.inorderLabels label := by
  have beforeEq := leavesBefore_eq before after whole distinct leaves
  have prefixLength : (labelsBefore label before.ancestors).length = (labelsBefore label after.ancestors).length := by
    rw [labelsBefore_length,labelsBefore_length,beforeEq]
  have focusLength : (before.focus.inorderLabels label).length = (after.focus.inorderLabels label).length := by
    have first := before.focus.inorderLabels_length label
    have second := after.focus.inorderLabels_length label
    rw [leaves] at first
    omega
  change (plug before.focus before.ancestors).inorderLabels label =
    (plug after.focus after.ancestors).inorderLabels label at order
  rw [labels_decomposition,labels_decomposition,List.append_assoc,List.append_assoc] at order
  exact (List.append_inj (List.append_inj order prefixLength).2 focusLength).1

theorem focus_eq (erase : ρ → τ) (label : ρ → ι)
    (injective : Function.Injective (fun record => (erase record,label record)))
    (before after : Cursor α ρ)
    (whole : before.tree.shape.leaves = after.tree.shape.leaves)
    (distinct : before.tree.shape.leaves.Nodup)
    (focus : before.focus.mapRecords erase = after.focus.mapRecords erase)
    (order : before.tree.inorderLabels label = after.tree.inorderLabels label) :
    before.focus = after.focus := by
  have leaves : before.focus.shape.leaves = after.focus.shape.leaves := by
    simpa only [Source.mapRecords_shape] using congrArg (fun tree : Source α τ => tree.shape.leaves) focus
  exact Source.eq_of_erasure_inorder erase label injective before.focus after.focus focus
    (focus_order label before after whole distinct leaves order)

end ChaCha.Paper20261030.SubtreeMetadata

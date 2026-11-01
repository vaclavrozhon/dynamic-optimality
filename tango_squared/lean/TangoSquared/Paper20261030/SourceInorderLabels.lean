import TangoSquared.Paper20261030.MultiSourceFingerLabels

set_option autoImplicit false

/-! The exact inorder word of immutable vertex labels. Rotations and
label-preserving writes retain this word, which is stronger than retaining
the multiset of identifiers. Together with a record erasure, it determines
all metadata in a tree of a given shape. -/

namespace TangoSquared.Paper20261030

open ColoredStorage SourcePointer SourceLocalProgram
open DynamicOptimality.LocalProgram (Move)

variable {α ρ τ ι : Type*}

def ColoredStorage.Source.inorderLabels (label : ρ → ι) : Source α ρ → List ι
  | .leaf _ record => [label record]
  | .fork record left right => left.inorderLabels label ++ label record :: right.inorderLabels label

theorem ColoredStorage.Source.inorderLabels_map (erase : ρ → τ) (label : τ → ι) (tree : Source α ρ) :
    (tree.mapRecords erase).inorderLabels label = tree.inorderLabels (label ∘ erase) := by
  induction tree <;> simp_all only [Source.mapRecords,Source.inorderLabels,Function.comp_def]

theorem ColoredStorage.Source.inorderLabels_length (label : ρ → ι) (tree : Source α ρ) :
    (tree.inorderLabels label).length + 1 = 2 * tree.shape.leaves.length := by
  induction tree <;> simp_all only [Source.inorderLabels,Source.shape,RouterProjection.Router.leaves,
    List.length_append,List.length_cons,List.length_nil] <;> omega

theorem ColoredStorage.Source.inorderLabels_setRoot (label : ρ → ι) (tree : Source α ρ) (fresh : ρ)
    (same : label fresh = label tree.rootRecord) :
    (tree.setRoot fresh).inorderLabels label = tree.inorderLabels label := by
  cases tree <;> simp_all only [Source.inorderLabels,Source.setRoot,Source.rootRecord]

theorem plug_inorderLabels_congr (label : ρ → ι) {before after : Source α ρ}
    (same : before.inorderLabels label = after.inorderLabels label) (outside : List (Frame α ρ)) :
    (plug before outside).inorderLabels label = (plug after outside).inorderLabels label := by
  induction outside generalizing before after with
  | nil => exact same
  | cons frame rest ih => cases frame with
    | left record sibling => exact ih (by simp only [Source.inorderLabels,same])
    | right sibling record => exact ih (by simp only [Source.inorderLabels,same])

theorem navigate_inorderLabels (label : ρ → ι) (action : Move) {before after : Cursor α ρ}
    (moved : navigate action before = some after) :
    before.tree.inorderLabels label = after.tree.inorderLabels label := by
  obtain ⟨focus,outside⟩ := before
  cases action with
  | left => cases focus with
    | leaf => simp [navigate] at moved
    | fork => cases Option.some.inj moved; rfl
  | right => cases focus with
    | leaf => simp [navigate] at moved
    | fork => cases Option.some.inj moved; rfl
  | up => cases outside with
    | nil => simp [navigate] at moved
    | cons frame rest => cases frame <;> cases Option.some.inj moved <;> rfl
  | rotateRight => cases focus with
    | leaf => simp [navigate] at moved
    | fork q left w => cases left with
      | leaf => simp [navigate] at moved
      | fork p u v =>
        cases Option.some.inj moved
        exact plug_inorderLabels_congr label
          (by simp only [Source.inorderLabels,List.append_assoc,List.cons_append]) outside
  | rotateLeft => cases focus with
    | leaf => simp [navigate] at moved
    | fork p u right => cases right with
      | leaf => simp [navigate] at moved
      | fork q v w =>
        cases Option.some.inj moved
        exact plug_inorderLabels_congr label
          (by simp only [Source.inorderLabels,List.append_assoc,List.cons_append]) outside

theorem ColoredStorage.Source.eq_of_erasure_inorder (erase : ρ → τ) (label : ρ → ι)
    (injective : Function.Injective (fun record => (erase record,label record)))
    (before after : Source α ρ) (same : before.mapRecords erase = after.mapRecords erase)
    (order : before.inorderLabels label = after.inorderLabels label) : before = after := by
  induction before generalizing after with
  | leaf key record =>
    cases after with
    | fork => cases same
    | leaf other fresh =>
      obtain ⟨keys,records⟩ := Source.leaf.inj same
      have labels := List.cons.inj order |>.1
      have values := injective (Prod.ext records labels)
      cases keys
      cases values
      rfl
  | fork record left right ihl ihr =>
    cases after with
    | leaf => cases same
    | fork fresh newLeft newRight =>
      obtain ⟨records,leftErases,rightErases⟩ := Source.fork.inj same
      have leafLengths : left.shape.leaves.length = newLeft.shape.leaves.length := by
        have shapes := congrArg (fun tree : Source α τ => tree.shape.leaves.length) leftErases
        simpa only [Source.mapRecords_shape] using shapes
      have sameLength : (left.inorderLabels label).length = (newLeft.inorderLabels label).length := by
        have hl := left.inorderLabels_length label
        have hr := newLeft.inorderLabels_length label
        omega
      have words := List.append_inj order sameLength
      have roots := List.cons.inj words.2
      have values := injective (Prod.ext records roots.1)
      rw [values,ihl _ leftErases words.1,ihr _ rightErases roots.2]

end TangoSquared.Paper20261030

namespace TangoSquared.Paper20261030.MultiSourceProgram

open ColoredStorage SourcePointer SourcePositions

variable {α ρ ι F σ : Type*} [DecidableEq F]

theorem Step.inorderLabels (label : ρ → ι) {source : Program σ F ρ} {state next : σ}
    {before after : Configuration F α ρ} {entry}
    (step : Step source state before next after entry)
    (stable : MultiSourceWriteLabels.Stable label (source state) before) :
    after.tree.inorderLabels label = before.tree.inorderLabels label := by
  cases step with
  | readNone | readSome | copy => rfl
  | nav instruction present reached moved =>
    rw [← locate_tree reached]
    exact (navigate_inorderLabels label _ moved).symm
  | write instruction present reached =>
    simp only [instruction,MultiSourceWriteLabels.Stable] at stable
    change (plug _ _).inorderLabels label = _
    rw [← locate_tree reached]
    exact plug_inorderLabels_congr label (Source.inorderLabels_setRoot _ _ _ (stable _ _ present reached)) _

end TangoSquared.Paper20261030.MultiSourceProgram

namespace TangoSquared.Paper20261030.MultiSourceWriteLabels

open MultiSourceProgram

variable {α ρ ι F σ : Type*} [DecidableEq F]

theorem Run.inorderLabels (label : ρ → ι) {source : Program σ F ρ} {state last : σ}
    {before after : Configuration F α ρ} {reads cost}
    (run : Run label source state before last after reads cost) :
    after.tree.inorderLabels label = before.tree.inorderLabels label := by
  induction run with
  | halt => rfl
  | next first stable rest ih => exact ih.trans (first.inorderLabels label stable)

end TangoSquared.Paper20261030.MultiSourceWriteLabels

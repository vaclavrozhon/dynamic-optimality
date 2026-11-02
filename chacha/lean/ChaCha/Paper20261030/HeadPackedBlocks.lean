import ChaCha.Paper20261030.PackedPortAgreement

/-!
# The common prefix and tails retain their actual physical packed blocks

These equalities use the actual exit-list decomposition of a primary head
step. They cover both colors and every source routing shape. The boundary
depth itself is excluded: it is the exchanged primary exit or the dormant
sentinel and is handled by the exposed constant-size head context.
-/

namespace ChaCha.Paper20261030.PackedPrimary

open PreferredProjection ColoredStorage PrimaryWings

variable {α ρ : Type*} [DecidableEq α]

theorem prefix_wing_agreement (before after : PrefRouter α) (common oldTail newTail : List (Exit α))
    (beforeWord : exits before = common ++ oldTail) (afterWord : exits after = common ++ newTail)
    (source : Source Nat ρ) (lower : ∀ d ∈ source.shape.leaves, d < common.length) (side : Bool) :
    wing 0 before side source = wing 0 after side source := by
  apply wing_congr
  intro d member
  rw [beforeWord,afterWord,portAt_prefix common oldTail d (lower d member),
    portAt_prefix common newTail d (lower d member)]

theorem tail_wing_agreement (whole tail : PrefRouter α) (common : List (Exit α)) (boundary : Exit α)
    (word : exits whole = common ++ boundary :: exits tail)
    (source : Source Nat ρ) (higher : ∀ d ∈ source.shape.leaves, common.length < d) (side : Bool) :
    wing 0 whole side source = wing (common.length+1) tail side source := by
  apply wing_congr
  intro d member
  rw [word,portAt_tail common (exits tail) boundary d (higher d member)]

theorem head_packed_blocks {x : α} {depth : Nat} {before after : PrefRouter α}
    (step : PrefRouter.HeadStep x depth before after) :
    ∃ (common : List (Exit α)) (old incoming : PrefRouter α) (oldRight : Bool),
      common.length = depth ∧
      exits before = common ++ ⟨oldRight,incoming⟩ :: exits old ∧
      exits after = common ++ ⟨!oldRight,old⟩ :: exits incoming ∧
      (∀ (source : Source Nat ρ), (∀ d ∈ source.shape.leaves, d < depth) → ∀ side,
        wing 0 before side source = wing 0 after side source) ∧
      (∀ (source : Source Nat ρ), (∀ d ∈ source.shape.leaves, depth < d) → ∀ side,
        wing 0 before side source = wing (depth+1) old side source) ∧
      (∀ (source : Source Nat ρ), (∀ d ∈ source.shape.leaves, depth < d) → ∀ side,
        wing 0 after side source = wing (depth+1) incoming side source) := by
  obtain ⟨common,old,incoming,oldRight,length,_,_,beforeWord,afterWord⟩ := head_exit_decomposition step
  refine ⟨common,old,incoming,oldRight,length,beforeWord,afterWord,?_,?_,?_⟩
  · intro source lower side
    exact prefix_wing_agreement before after common _ _ beforeWord afterWord source
      (fun d member => by simpa only [length] using lower d member) side
  · intro source higher side
    simpa only [length] using tail_wing_agreement before old common _ beforeWord source
      (fun d member => by simpa only [length] using higher d member) side
  · intro source higher side
    simpa only [length] using tail_wing_agreement after incoming common _ afterWord source
      (fun d member => by simpa only [length] using higher d member) side

end ChaCha.Paper20261030.PackedPrimary

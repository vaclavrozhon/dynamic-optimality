import TangoSquared.Paper20261030.PreparedPhysicalHeadExchange

/-!
# Supplying the actual complete virtual headers to physical traces

The total header function agrees with `Input.completeHeader` on every
valid active or dormant source. Its fallback is used only outside those
leaf-word invariants. This specifies header contents; it does not replace
the obligation to acquire them through local reads during execution.
-/

namespace TangoSquared.Paper20261030.PackedPrimary

open ColoredStorage PreferredProjection PrimaryWings

variable {α ρ : Type*} [DecidableEq α]

abbrev ValidInput (start : Nat) (primary : PrefRouter α) (source : Source Nat ρ) : Prop :=
  source.shape.leaves = List.range' start ((exits primary).length+1) ∨
    (0 < start ∧ source.shape.leaves = (start-1) :: List.range' start ((exits primary).length+1))

instance validInputDecidable (start : Nat) (primary : PrefRouter α) (source : Source Nat ρ) :
    Decidable (ValidInput start primary source) := inferInstanceAs (Decidable (_ ∨ _))

def canonicalHeaders (start : Nat) (primary : PrefRouter α) (source : Source Nat ρ) : List (Datum ρ) :=
  if valid : ValidInput start primary source then
    (Input.mk start source valid).completeHeader
  else []

theorem canonicalHeaders_input {primary : PrefRouter α} (input : Input primary ρ) :
    canonicalHeaders input.start primary input.source = input.completeHeader := by
  rw [canonicalHeaders,dif_pos input.leaves]

theorem canonicalHeaders_size (start : Nat) (primary : PrefRouter α) (source : Source Nat ρ) :
    (canonicalHeaders start primary source).length ≤ 1 := by
  unfold canonicalHeaders
  split <;> simp [Input.completeHeader]

theorem canonical_encoding_tree {primary : PrefRouter α} (input : Input primary ρ)
    (payload : Exit α → Source α (List (Option (Datum ρ)))) :
    (encoding input.start primary payload (canonicalHeaders input.start primary input.source)).tree
      Datum.record input.source = input.physical payload := by
  rw [canonicalHeaders_input]
  exact input.encoding_tree payload

theorem nestedTree_canonical {outer inner : PrefRouter α} (outerInput : Input outer ρ) (innerInput : Input inner ρ)
    (direction : Bool) (depth : Nat) (outerStart : outerInput.start = 0) (innerStart : innerInput.start = depth+1)
    (payload : Exit α → Source α (List (Option (Datum ρ)))) :
    nestedTree Datum.record payload canonicalHeaders outer inner direction depth outerInput.source innerInput.source =
      outerInput.physical (Function.update payload ⟨direction,inner⟩ (innerInput.physical payload)) := by
  unfold nestedTree
  rw [← innerStart,canonical_encoding_tree innerInput]
  rw [← outerStart,canonical_encoding_tree outerInput]

end TangoSquared.Paper20261030.PackedPrimary

namespace TangoSquared.PreferredProjection.PrefRouter

variable {α : Type*} [DecidableEq α]

theorem HeadStep.perfect {x : α} {d h : Nat} {before after : PrefRouter α}
    (step : HeadStep x d before after) (perfectBefore : before.Perfect h) : after.Perfect h := by
  induction step generalizing h with
  | leftRoot => cases h <;> exact perfectBefore
  | rightRoot => cases h <;> exact perfectBefore
  | leftDown right step ih =>
    cases h with
    | zero => exact False.elim perfectBefore
    | succ h => exact ⟨ih perfectBefore.1,perfectBefore.2⟩
  | rightDown left notLeft step ih =>
    cases h with
    | zero => exact False.elim perfectBefore
    | succ h => exact ⟨perfectBefore.1,ih perfectBefore.2⟩

end TangoSquared.PreferredProjection.PrefRouter

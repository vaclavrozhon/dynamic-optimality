import ChaCha.Paper20261030.PhysicalHeadExchange
import ChaCha.Paper20261030.HeadPackedBlocks

/-!
# Packed physical blocks depend only on their retained ports

Color agreement preserves the owner of every connector record. Payloads
need agree only at retained real ports; virtual leaves have no physical
payload. The induction includes mirroring before payload attachment.
-/

namespace ChaCha.Paper20261030.ProjectionLocal

open ColoredStorage RouterProjection

variable {κ α β ρ τ C : Type*} [LinearOrder C]

theorem physicalProjection_congr (oldColor newColor : κ → C) (q : C)
    (oldLabels newLabels : κ → α) (values : ρ → τ)
    (oldPayload newPayload : α → Source β (List (Option τ))) (reverse : Bool) (source : Source κ ρ)
    (colors : ∀ key ∈ source.shape.leaves, oldColor key = newColor key)
    (payloads : ∀ key ∈ source.shape.leaves, oldColor key = q →
      oldPayload (oldLabels key) = newPayload (newLabels key)) :
    physicalProjection oldColor q oldLabels values oldPayload reverse source =
      physicalProjection newColor q newLabels values newPayload reverse source := by
  induction source with
  | leaf key record =>
    have member : key ∈ (Source.leaf key record).shape.leaves := by simp [Source.shape,Router.leaves]
    rw [physicalProjection_leaf,physicalProjection_leaf,← colors key member]
    split
    · rw [payloads key member (by assumption)]
    · rfl
  | fork record left right ihl ihr =>
    have lc := fun key member => colors key (List.mem_append_left right.shape.leaves member)
    have rc := fun key member => colors key (List.mem_append_right left.shape.leaves member)
    have lp := fun key member => payloads key (List.mem_append_left right.shape.leaves member)
    have rp := fun key member => payloads key (List.mem_append_right left.shape.leaves member)
    have owners := owner_color_congr oldColor newColor left right
      (left.support_congr oldColor newColor lc) (right.support_congr oldColor newColor rc)
    simp only [physicalProjection_fork,physicalConnector,owners,ihl lc lp,ihr rc rp]

end ChaCha.Paper20261030.ProjectionLocal

namespace ChaCha.Paper20261030.PackedPrimary

open ColoredStorage ProjectionLocal PreferredProjection PrimaryWings

variable {α ρ τ : Type*} [DecidableEq α]

local instance physicalPortColorOrder : LinearOrder (Option Bool) :=
  inferInstanceAs (LinearOrder (WithBot Bool))

def encoding (start : Nat) (primary : PrefRouter α)
    (payload : Exit α → Source α (List (Option τ))) (header : List τ) :
    HeadBlocks.Encoding Nat (Exit α) α τ :=
  ⟨color start primary,label start primary,payload,primary.terminal,header⟩

set_option backward.isDefEq.respectTransparency false in
theorem encoding_wing_congr (oldStart newStart : Nat) (oldPrimary newPrimary : PrefRouter α)
    (oldPayload newPayload : Exit α → Source α (List (Option τ))) (oldHeader newHeader : List τ)
    (values : ρ → τ) (source : Source Nat ρ) (side : Bool)
    (ports : ∀ d ∈ source.shape.leaves,
      portAt oldStart (exits oldPrimary) d = portAt newStart (exits newPrimary) d)
    (payloads : ∀ d ∈ source.shape.leaves, ∀ exit,
      portAt oldStart (exits oldPrimary) d = some exit → oldPayload exit = newPayload exit) :
    (encoding oldStart oldPrimary oldPayload oldHeader).wing values side source =
      (encoding newStart newPrimary newPayload newHeader).wing values side source := by
  apply physicalProjection_congr
  · intro d member
    exact congrArg (Option.map Exit.leftOfEndpoint) (ports d member)
  · intro d member retained
    change color oldStart oldPrimary d = some side at retained
    change oldPayload (label oldStart oldPrimary d) = newPayload (label newStart newPrimary d)
    unfold label
    rw [← ports d member]
    cases port : portAt oldStart (exits oldPrimary) d with
    | none => simp [color,port] at retained
    | some exit => exact payloads d member exit port

end ChaCha.Paper20261030.PackedPrimary

import ChaCha.Paper20261030.PackedPrimaryPlan
import ChaCha.Paper20261030.PrimaryHeadBlocks

/-!
# Unchanged depth blocks have identical actual packed primary wings

Packing depends on colors only at leaves present in a source block.
Relabeling a retained real port depends only on its actual exit, never on
the fallback used for virtual leaves. Thus equality of the exit lookup
on a whole source block implies equality of both physical routing wings.
The depth lookup lemmas identify the common prefix and unchanged tails
at the boundary of an actual primary head switch.
-/

namespace ChaCha.Paper20261030.ColoredStorage

open RouterProjection

variable {α ρ C : Type*} [LinearOrder C]

theorem Source.support_congr (source : Source α ρ) (color fresh : α → C)
    (same : ∀ key ∈ source.shape.leaves, color key = fresh key) : source.support color = source.support fresh := by
  induction source with
  | leaf key record => simp only [Source.shape,Router.leaves,List.mem_singleton] at same; simp [Source.support,same key rfl]
  | fork record l r ihl ihr =>
    have hl := ihl (fun key member => same key (List.mem_append_left _ member))
    have hr := ihr (fun key member => same key (List.mem_append_right _ member))
    simp only [Source.support,hl,hr]

theorem owner_color_congr (color fresh : α → C) (l r : Source α ρ)
    (left : l.support color = l.support fresh) (right : r.support color = r.support fresh) :
    owner color l r = owner fresh l r := by
  unfold owner
  simp only [left,right]

theorem pack_congr (source : Source α ρ) (color fresh : α → C) (q : C)
    (same : ∀ key ∈ source.shape.leaves, color key = fresh key) : pack color q source = pack fresh q source := by
  induction source with
  | leaf key record => simp only [pack,same key (by simp [Source.shape,Router.leaves])]
  | fork record l r ihl ihr =>
    have left := fun key member => same key (List.mem_append_left r.shape.leaves member)
    have right := fun key member => same key (List.mem_append_right l.shape.leaves member)
    have ownerSame := owner_color_congr color fresh l r (l.support_congr color fresh left) (r.support_congr color fresh right)
    simp only [pack,ownerSame,ihl left,ihr right]

theorem packed_congr (source : Source α ρ) (color fresh : α → C) (q : C)
    (same : ∀ key ∈ source.shape.leaves, color key = fresh key) : packed color q source = packed fresh q source := by
  unfold packed
  rw [pack_congr source color fresh q same]

theorem Source.relabel_congr {β : Type*} (source : Source α ρ) (before after : α → β)
    (same : ∀ key ∈ source.shape.leaves, before key = after key) : source.relabel before = source.relabel after := by
  induction source with
  | leaf key record => simp only [Source.relabel,same key (by simp [Source.shape,Router.leaves])]
  | fork record l r ihl ihr =>
    have left := ihl (fun key member => same key (List.mem_append_left _ member))
    have right := ihr (fun key member => same key (List.mem_append_right _ member))
    simp only [Source.relabel,left,right]

end ChaCha.Paper20261030.ColoredStorage

namespace ChaCha.Paper20261030.PackedPrimary

open PreferredProjection RouterProjection ColoredStorage PrimaryWings

variable {α ρ : Type*} [DecidableEq α]

local instance portAgreementColorOrder : LinearOrder (Option Bool) := inferInstanceAs (LinearOrder (WithBot Bool))

set_option backward.isDefEq.respectTransparency false in
theorem wing_congr (oldStart newStart : Nat) (old fresh : PrefRouter α) (side : Bool) (source : Source Nat ρ)
    (ports : ∀ d ∈ source.shape.leaves, portAt oldStart (exits old) d = portAt newStart (exits fresh) d) :
    wing oldStart old side source = wing newStart fresh side source := by
  have colors : ∀ d ∈ source.shape.leaves, color oldStart old d = color newStart fresh d := by
    intro d member
    simp only [color,ports d member]
  have packing := packed_congr source (color oldStart old) (color newStart fresh) (some side) colors
  unfold wing
  rw [packing]
  cases present : packed (color newStart fresh) (some side) source with
  | none => rfl
  | some actual =>
    simp only [Option.map_some,Option.some.injEq]
    apply Source.relabel_congr
    intro d member
    have retained : d ∈ source.shape.leaves ∧ color newStart fresh d = some side := by
      rw [packed_shape _ _ _ present,Router.leaves_prune] at member
      simpa only [List.mem_filter,keepColor,decide_eq_true_eq] using member
    unfold label
    rw [ports d retained.1]
    cases value : portAt newStart (exits fresh) d with
    | none =>
      simp only [color,value,Option.map_none] at retained
      have impossible := retained.2
      cases impossible
    | some exit => rfl

end ChaCha.Paper20261030.PackedPrimary

namespace ChaCha.Paper20261030.PrimaryWings

variable {β : Type*}

theorem portAt_prefix (common suffix : List β) (depth : Nat) (inside : depth < common.length) :
    portAt 0 (common ++ suffix) depth = portAt 0 common depth := by
  simp only [portAt,Nat.zero_le,if_true,Nat.sub_zero,List.getElem?_append_left inside]

theorem portAt_tail (common tail : List β) (boundary : β) (depth : Nat) (below : common.length < depth) :
    portAt 0 (common ++ boundary :: tail) depth = portAt (common.length+1) tail depth := by
  have beyond : common.length ≤ depth := by omega
  have positive : common.length+1 ≤ depth := by omega
  have index : depth-common.length = (depth-(common.length+1))+1 := by omega
  simp only [portAt,Nat.zero_le,if_true,Nat.sub_zero,List.getElem?_append_right beyond,
    positive,if_true,index,List.getElem?_cons_succ]

end ChaCha.Paper20261030.PrimaryWings

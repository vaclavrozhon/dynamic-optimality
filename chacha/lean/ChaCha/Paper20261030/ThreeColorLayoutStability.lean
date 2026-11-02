import ChaCha.Paper20261030.ThreeColorConfiguration

/-! A successfully assembled connector contains every listed color.
Together with coverage this fixes precisely the present colors. Therefore
a component run preserving its connector layout also preserves its wing
bits, and its final root configuration is the canonical three-piece one.
-/

namespace ChaCha.Paper20261030.ForestConnector

open ColoredStorage SourcePointer

variable {α ρ C : Type*} [DecidableEq C]

theorem assemble_member (forest : ProjectionForest.State C α ρ) (layout : Source C Unit)
    (config : MultiSourceProgram.Configuration C α (List ρ)) (represented : assemble forest layout = some config)
    (q : C) (member : q ∈ colors layout) : (forest q).isSome = true := by
  induction layout generalizing config with
  | leaf selected value =>
    have equal : q = selected := by simpa only [colors,Source.shape,RouterProjection.Router.leaves,List.mem_singleton] using member
    subst selected
    cases h : forest q with
    | none => simp only [assemble,h,Option.map_none,reduceCtorEq] at represented
    | some current => rfl
  | fork value left right ihl ihr =>
    obtain ⟨l,r,leftRep,rightRep,_⟩ := assemble_fork represented
    have either : q ∈ colors left ∨ q ∈ colors right := by
      simpa only [colors,Source.shape,RouterProjection.Router.leaves,List.mem_append] using member
    exact either.elim (ihl l leftRep) (ihr r rightRep)

theorem present_iff_member (forest : ProjectionForest.State C α ρ) (layout : Source C Unit)
    (config : MultiSourceProgram.Configuration C α (List ρ)) (represented : assemble forest layout = some config)
    (covered : Covers layout forest) (q : C) : (forest q).isSome = true ↔ q ∈ colors layout := by
  constructor
  · intro present
    cases h : forest q with
    | none => simp only [h,Option.isSome_none,Bool.false_eq_true] at present
    | some current => exact covered q current h
  · exact assemble_member forest layout config represented q

theorem same_presence (layout : Source C Unit) (before after : ProjectionForest.State C α ρ)
    (initial final : MultiSourceProgram.Configuration C α (List ρ))
    (initialRep : assemble before layout = some initial) (finalRep : assemble after layout = some final)
    (initialCovered : Covers layout before) (finalCovered : Covers layout after) (q : C) :
    (after q).isSome = (before q).isSome := by
  have equal := (present_iff_member after layout final finalRep finalCovered q).trans
    (present_iff_member before layout initial initialRep initialCovered q).symm
  cases ha : (after q).isSome <;> cases hb : (before q).isSome <;> simp_all

end ChaCha.Paper20261030.ForestConnector

namespace ChaCha.Paper20261030.ForestConnector.ThreeColors

open ColoredStorage SourcePointer

variable {α ρ : Type*}

theorem layout_congr (before after : ProjectionForest.State (Option Bool) α ρ)
    (present : ∀ q, (after q).isSome = (before q).isSome) : layout after = layout before := by
  simp only [layout,present]

theorem canonical_final (before after : ProjectionForest.State (Option Bool) α ρ)
    (initial final : MultiSourceProgram.Configuration (Option Bool) α (List ρ))
    (initialRep : assemble before (layout before) = some initial)
    (finalRep : assemble after (layout before) = some final)
    (covered : Covers (layout before) after) (header : Source α (List ρ))
    (headerPresent : after none = some ⟨header,[]⟩) :
    (∀ q, (after q).isSome = (before q).isSome) ∧ final = configuration after ⟨header,[]⟩ := by
  have present := same_presence (layout before) before after initial final initialRep finalRep (covers before) covered
  refine ⟨present,?_⟩
  have assembled := assemble_configuration after ⟨header,[]⟩ headerPresent
  rw [layout_congr before after present,finalRep] at assembled
  exact Option.some.inj assembled

end ChaCha.Paper20261030.ForestConnector.ThreeColors

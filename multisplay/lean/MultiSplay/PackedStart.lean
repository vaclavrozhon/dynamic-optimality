import MultiSplay.PackedInitialization
import MultiSplay.InterfacePackingExcess

/-! # Constructive forest initialization with a linear, universe-free budget -/

noncomputable section

namespace MultiSplay.PackedSplay

open Splay.Interface (Parameters)
open Splay.Rank (Snapshot)
open Splay.Lazy.Canonical
open SharedSplay
open InterfacePacking (pack neutral)

variable {m : Nat} {params : Parameters}

theorem initial_excess (forest : List (Trees m))
    (cap : ∀ trees ∈ forest, Splay.Analysis.contractedGap (Snapshot.ofTree trees.comparison).withTruePriority.maxRank ≤ params.valueBound) :
    (forest.map (fun trees => InterfaceForest.excess trees.emptyComponent.source)).sum ≤ params.valueBound * Trees.mass forest := by
  induction forest with
  | nil => exact Nat.le_refl _
  | cons head tail ih =>
      have valid := (emptyCanonicalState_toInterface_initial
        (Snapshot.ofTree head.comparison).withTruePriority head.splay params (cap head (List.mem_cons_self))).1
      have balance := InterfaceForest.excess_add_card valid
      have values := Splay.Interface.State.totalValue_le valid
      have rest := ih (fun trees member => cap trees (List.mem_cons_of_mem _ member))
      change InterfaceForest.excess head.emptyComponent.source + (2*head.size+1) = _ at balance
      simp only [List.map_cons, List.sum_cons, Trees.mass] at rest ⊢
      nlinarith

theorem canonical_start (forest : List (Trees m))
    (separate : forest.Pairwise Trees.Disjoint) (growingLimit : 2 ≤ params.growingLimit)
    (cap : ∀ trees ∈ forest, Splay.Analysis.contractedGap (Snapshot.ofTree trees.comparison).withTruePriority.maxRank ≤ params.valueBound) :
    ∃ initial first : Splay.Interface.State m, ∃ setup : Initialization params initial first,
      initial.Initial params ∧ InterfaceForest.excess initial ≤ params.valueBound * Trees.mass forest ∧
      setup.mass = Trees.mass forest ∧ Nonempty (Packing params (forest.map Trees.canonical) first) := by
  let initial := pack (neutral m) (forest.map Trees.emptyComponent)
  have initialSeparate : (forest.map Trees.emptyComponent).Pairwise InterfacePacking.Component.Disjoint := by
    rw [List.pairwise_map]
    exact separate
  have initialValid : initial.Valid params := by
    apply InterfacePacking.valid _ _ (InterfacePacking.neutral_closed m).valid initialSeparate
    · intro component member
      obtain ⟨trees, present, rfl⟩ := List.mem_map.mp member
      exact (emptyCanonicalState_toInterface_initial _ _ params (cap trees present)).1
    · exact fun component _ => (InterfacePacking.neutral_closed m).passive component.element
  have initialized : initial.Initial params := by
    refine ⟨initialValid, ?_⟩
    apply InterfacePacking.pack_empty_blocks _ _ rfl
    intro component member
    obtain ⟨trees, _, rfl⟩ := List.mem_map.mp member
    rfl
  obtain ⟨first, setup, mass, same, finalSeparate⟩ := initialize_forest forest (neutral m)
    (InterfacePacking.neutral_closed m) [] (by simpa using initialSeparate)
    (by intro component member; cases member) growingLimit cap initial
    (by simpa only [List.append_nil] using (show InterfacePermutation.Equivalent initial initial from ⟨List.Perm.refl _, rfl⟩))
  refine ⟨initial, first, setup, initialized, ?_, mass,
    ⟨⟨neutral m, InterfacePacking.neutral_closed m, by simpa using finalSeparate, ?_, by simpa using same⟩⟩⟩
  · have paid := InterfacePacking.pack_excess (neutral m) (forest.map Trees.emptyComponent)
    have empty : InterfaceForest.excess (neutral m) = 0 := InterfaceForest.neutral_excess _ (fun _ => rfl)
    rw [empty, Nat.zero_add] at paid
    exact paid.trans (by simpa only [List.map_map, Function.comp_def] using initial_excess forest cap)
  · intro component member
    obtain ⟨trees, present, rfl⟩ := List.mem_map.mp member
    exact SharedSplay.canonical_certified trees.comparison trees.splay growingLimit (cap trees present)

end MultiSplay.PackedSplay

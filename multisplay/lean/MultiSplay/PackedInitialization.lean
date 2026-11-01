import MultiSplay.PackedSplay
import MultiSplay.CanonicalComponentStart

/-! # One actual initialization of all packed components -/

noncomputable section

namespace MultiSplay.PackedSplay

open Splay.Accounting
open Splay.Interface (Element Parameters)
open Splay.Rank (Snapshot)
open Splay.Lazy.Canonical
open SharedSplay
open InterfacePacking (pack)

variable {m : Nat} {params : Parameters}

def Trees.Disjoint (a b : Trees m) : Prop := ∀ x y, a.element x ≠ b.element y

def Trees.emptyComponent (trees : Trees m) : InterfacePacking.Component m :=
  ⟨trees.size, (emptyCanonicalState (Snapshot.ofTree trees.comparison).withTruePriority trees.splay).toInterface,
    trees.element, trees.injective⟩

def Trees.canonical (trees : Trees m) : Local m :=
  ⟨trees, canonicalState (Snapshot.ofTree trees.comparison).withTruePriority trees.splay⟩

def Trees.mass (forest : List (Trees m)) : Nat := (forest.map (fun trees => 2*trees.size+1)).sum

/-- Initialize a list beside any valid disjoint current histories. Both the
strict trace and the final packing are constructed recursively. -/
theorem initialize_forest (forest : List (Trees m)) (archive : Splay.Interface.State m)
    (closed : InterfacePacking.Closed archive) (others : List (InterfacePacking.Component m))
    (separate : (forest.map Trees.emptyComponent ++ others).Pairwise InterfacePacking.Component.Disjoint)
    (sources : ∀ component ∈ others, component.source.Valid params)
    (growingLimit : 2 ≤ params.growingLimit)
    (cap : ∀ trees ∈ forest, Splay.Analysis.contractedGap (Snapshot.ofTree trees.comparison).withTruePriority.maxRank ≤ params.valueBound)
    (whole : Splay.Interface.State m)
    (same : InterfacePermutation.Equivalent (pack archive (forest.map Trees.emptyComponent ++ others)) whole) :
    ∃ final : Splay.Interface.State m, ∃ setup : Initialization params whole final,
      setup.mass = Trees.mass forest ∧
      InterfacePermutation.Equivalent (pack archive (components (forest.map Trees.canonical) ++ others)) final ∧
      (components (forest.map Trees.canonical) ++ others).Pairwise InterfacePacking.Component.Disjoint := by
  induction forest generalizing others whole with
  | nil => exact ⟨whole, .done whole, rfl, same, separate⟩
  | cons head tail ih =>
      let rest := tail.map Trees.emptyComponent ++ others
      have restValid : ∀ component ∈ rest, component.source.Valid params := by
        intro component member
        rcases List.mem_append.mp member with fresh | old
        · obtain ⟨trees, present, rfl⟩ := List.mem_map.mp fresh
          exact (emptyCanonicalState_toInterface_initial _ _ params (cap trees (List.mem_cons_of_mem _ present))).1
        · exact sources component old
      let selected := InterfacePacking.headFrame archive head.emptyComponent rest closed.valid separate restValid
        (fun component _ => closed.passive component.element)
      let framed : InterfaceFramedTrace.Framed params head.emptyComponent.source whole :=
        {selected with equivalent := ⟨selected.equivalent.1.trans same.1, selected.equivalent.2.trans same.2⟩}
      obtain ⟨setup⟩ := setup_exists (Snapshot.ofTree head.comparison).withTruePriority head.splay
        growingLimit (cap head (List.mem_cons_self)) whole framed
      have afterEq := setup.framed.equivalent
      rw [setup.element_eq, setup.frame_eq] at afterEq
      change InterfacePermutation.Equivalent (pack archive (head.canonical.component :: rest)) setup.final at afterEq
      have afterSeparate : (head.canonical.component :: rest).Pairwise InterfacePacking.Component.Disjoint := by
        simpa only [List.map_cons, List.cons_append, rest, List.pairwise_cons, Trees.emptyComponent, Trees.canonical, Local.component,
          InterfacePacking.Component.Disjoint] using separate
      have order : (head.canonical.component :: rest).Perm
          (tail.map Trees.emptyComponent ++ head.canonical.component :: others) := List.perm_middle.symm
      have reordered := InterfacePacking.perm archive order afterSeparate
      have newSame : InterfacePermutation.Equivalent
          (pack archive (tail.map Trees.emptyComponent ++ head.canonical.component :: others)) setup.final :=
        ⟨reordered.1.symm.trans afterEq.1, reordered.2.symm.trans afterEq.2⟩
      have otherValid : ∀ component ∈ head.canonical.component :: others, component.source.Valid params := by
        intro component member
        rcases List.mem_cons.mp member with rfl | member
        · exact (canonical_certified head.comparison head.splay growingLimit (cap head (List.mem_cons_self))).represented.valid.1
        · exact sources component member
      obtain ⟨final, later, mass, finalEq, finalSeparate⟩ := ih (head.canonical.component :: others)
        (order.pairwise afterSeparate (fun h => h.symm)) otherValid
        (fun trees member => cap trees (List.mem_cons_of_mem _ member)) setup.final newSame
      have finalOrder : (components (tail.map Trees.canonical) ++ head.canonical.component :: others).Perm
          (head.canonical.component :: (components (tail.map Trees.canonical) ++ others)) := List.perm_middle
      have finalReordered := InterfacePacking.perm archive finalOrder finalSeparate
      refine ⟨final, .next setup (cap head (List.mem_cons_self)) rfl later, ?_, ?_, ?_⟩
      · simp only [Initialization.mass, Trees.mass, List.map_cons, List.sum_cons] at mass ⊢
        exact congrArg (2 * head.size + 1 + ·) mass
      · exact ⟨finalReordered.1.symm.trans finalEq.1, finalReordered.2.symm.trans finalEq.2⟩
      · exact finalOrder.pairwise finalSeparate (fun h => h.symm)

end MultiSplay.PackedSplay

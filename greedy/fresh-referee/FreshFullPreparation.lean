import FreshComparatorPreparation
import HeapCutProgram

/-!
Complete fresh parameter realization for the existing prepareComparator.
Conversion stages use disjoint fixed-width ranges. The cut tail then uses
state-dependent reservation widths computed from its actual intermediate
states. This module supplies concrete parameters, not freshness premises.
-/
namespace GreedyMerge.HeapAllocation

open OrderedBlocks FreshIds
open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Lazy.Canonical

theorem detachPorts_ids_congr {n : ℕ} (before : BST 0 n) (families first second : NameSupply n)
    (ports : List ℕ) (stage : ℕ) (states : HeapSides n)
    (agree : ∀ query,stage≤query → query<stage+ports.length → first query=second query) :
    detachPorts before families first ports stage states = detachPorts before families second ports stage states := by
  induction ports generalizing stage states with
  | nil => rfl
  | cons record rest ih =>
      have head := agree stage (le_refl _) (by simp)
      simp only [detachPorts,head]
      rw [ih (stage+1) _ (by intro query lo hi;apply agree query (by omega);simp only [List.length_cons];omega)]

noncomputable def prefixThenCuts {n : ℕ} (prefixNames cutNames : NameSupply n) (offset : ℕ) : NameSupply n :=
  fun stage => if stage<offset then prefixNames stage else cutNames (stage-offset)

theorem prefixThenCuts_before {n : ℕ} (prefixNames cutNames : NameSupply n) (offset stage : ℕ)
    (before : stage<offset) : prefixThenCuts prefixNames cutNames offset stage=prefixNames stage := by
  simp [prefixThenCuts,before]

theorem prefixThenCuts_tail {n : ℕ} (prefixNames cutNames : NameSupply n) (offset : ℕ) :
    (fun stage => prefixThenCuts prefixNames cutNames offset (stage+offset))=cutNames := by
  funext stage
  simp only [prefixThenCuts,show ¬stage+offset<offset by omega,if_false,Nat.add_sub_cancel_right]

structure FreshPreparation (n : ℕ) where
  families : NameSupply n
  ids : NameSupply n
  states : HeapSides n
  next : ℕ

noncomputable def allocateComparatorPreparation {n depth : ℕ} {before after : BST 0 n}
    (profile : RotationCutProfile before after depth) (ports : List ℕ) (owners : Finset (External n))
    (start : ℕ) (states : HeapSides n) : FreshPreparation n :=
  let names := sequenceNames start
  let prepared := preparedForCuts before after start ports owners states
  let cuts := allocateCuts profile.entries (start+Fintype.card (Place n)*(ports.length+2)) prepared
  ⟨names,prefixThenCuts names cuts.names (ports.length+2),cuts.states,cuts.next⟩

theorem allocateComparatorPreparation_eq {n depth : ℕ} {before after : BST 0 n}
    (profile : RotationCutProfile before after depth) (ports : List ℕ) (owners : Finset (External n))
    (start : ℕ) (states : HeapSides n) :
    let result := allocateComparatorPreparation profile ports owners start states
    (prepareComparator profile result.families result.ids ports owners states).1=result.states := by
  let names := sequenceNames (n:=n) start
  let prepared := preparedForCuts before after start ports owners states
  let cuts := allocateCuts profile.entries (start+Fintype.card (Place n)*(ports.length+2)) prepared
  let combined := prefixThenCuts names cuts.names (ports.length+2)
  have atZero : combined 0=names 0 := prefixThenCuts_before names cuts.names _ _ (by omega)
  have atSeal : combined (ports.length+1)=names (ports.length+1) :=
    prefixThenCuts_before names cuts.names _ _ (by omega)
  have atDetach (initial : HeapSides n) : detachPorts before names combined ports 1 initial =
      detachPorts before names names ports 1 initial := by
    apply detachPorts_ids_congr
    intro query lo hi
    exact prefixThenCuts_before names cuts.names _ _ (by omega)
  change (prepareCuts combined profile.entries (ports.length+2)
    (sealOwners before owners (names (ports.length+1)) (combined (ports.length+1))
      (detachPorts before names combined ports 1
        (prepareAllGrowers before after (names 0) (combined 0) states)).1)).1=cuts.states
  rw [atZero,atSeal,atDetach]
  change (prepareCuts combined profile.entries (ports.length+2) prepared).1=cuts.states
  rw [show ports.length+2=0+(ports.length+2) by omega,prepareCuts_shift]
  rw [prefixThenCuts_tail]
  exact congrArg Prod.fst (allocateCuts_eq profile.entries _ prepared)

theorem allocateComparatorPreparation_inventory {n depth : ℕ} {before after : BST 0 n}
    (profile : RotationCutProfile before after depth) (ports : List ℕ) (owners : Finset (External n))
    (start : ℕ) (states : HeapSides n) (inventory : HeapInventory states start) :
    HeapInventory (allocateComparatorPreparation profile ports owners start states).states
      (allocateComparatorPreparation profile ports owners start states).next := by
  exact allocateCuts_inventory profile.entries _ _ (preparedForCuts_inventory before after start ports owners states inventory)

theorem allocateComparatorPreparation_monotone {n depth : ℕ} {before after : BST 0 n}
    (profile : RotationCutProfile before after depth) (ports : List ℕ) (owners : Finset (External n))
    (start : ℕ) (states : HeapSides n) : start≤(allocateComparatorPreparation profile ports owners start states).next := by
  exact (Nat.le_add_right _ _).trans (allocateCuts_next profile.entries _ _)

#print axioms allocateComparatorPreparation_eq
#print axioms allocateComparatorPreparation_inventory
#print axioms allocateComparatorPreparation_monotone

end GreedyMerge.HeapAllocation

import CanonicalBridge
import RefinementRotationHeap

/-!
One direct composition of independently verified structural modules.
Under actual neighborhood-owner canonical predicates, a comparator rotation
is followed by at most two fixed-rank refinement rotations. Their combined
heap-parent support has at most eight records. No abstract locality or
five-port realization hypothesis remains in this statement.
-/

namespace GreedyMerge.Assembly

open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Lazy.Canonical
open PortCases RefinementRotation

theorem rotationSteps_parent_support {n steps : ℕ} (snapshot : Snapshot n)
    {before after : BST 0 n} (rotations : RotationSteps steps before after) :
    ∃ selected : Finset (External n), selected.card ≤ 4 * steps ∧
      ∀ child, child ∉ selected →
        canonicalParent snapshot after child = canonicalParent snapshot before child := by
  classical
  induction steps generalizing before with
  | zero => cases rotations; exact ⟨∅, by simp, fun _ _ => rfl⟩
  | succ steps ih =>
    cases rotations with
    | cons first rest =>
        obtain ⟨firstSupport, firstCard, firstPreserved⟩ := rotation_parent_support snapshot first
        obtain ⟨restSupport, restCard, restPreserved⟩ := ih rest
        refine ⟨firstSupport ∪ restSupport, ?_, ?_⟩
        · have bound := Finset.card_union_le firstSupport restSupport
          omega
        · intro child outside
          have notFirst : child ∉ firstSupport := fun member => outside (Finset.mem_union_left _ member)
          have notRest : child ∉ restSupport := fun member => outside (Finset.mem_union_right _ member)
          exact (restPreserved child notRest).trans (firstPreserved child notFirst)

/-- Fully concrete support for recanonicalization after one comparator
rotation: at most eight individual heap records need reparenting. -/
theorem recanonicalization_parent_support {height : ℕ → ℤ} {n depth : ℕ}
    {before after : BST 0 n} (step : RotationAt depth before after)
    (oldOwner newOwner : ℕ → ℕ)
    (oldOwners : Surface.Owners height before.depth oldOwner n)
    (newOwners : Surface.Owners height after.depth newOwner n)
    (oldTree newTree : BST 0 n)
    (oldCanonical : Surface.Canonical height (fun key => before.depth (oldOwner key)) oldTree)
    (newCanonical : Surface.Canonical height (fun key => after.depth (newOwner key)) newTree) :
    ∃ selected : Finset (External n), selected.card ≤ 8 ∧
      ∀ child, child ∉ selected →
        canonicalParent (Snapshot.ofTree after) newTree child =
          canonicalParent (Snapshot.ofTree after) oldTree child := by
  obtain ⟨steps, stepsBound, rotations⟩ := CanonicalBridge.actual_canonical_rotationAt step
    oldOwner newOwner oldOwners newOwners oldTree newTree oldCanonical newCanonical
  obtain ⟨selected, cardinal, preserved⟩ := rotationSteps_parent_support (Snapshot.ofTree after) rotations
  exact ⟨selected, by omega, preserved⟩

/-- Compose the rank change and the actual recanonicalization. Away from
ten selected records, every final parent is unchanged or the record moves
from the demoted comparator key to the promoted key. The bulk move may
contain arbitrarily many records; it is deliberately not counted as ten
individual updates. Its ordered-block implementation is a separate step. -/
theorem canonical_update_parent_relation {height : ℕ → ℤ} {n a b depth : ℕ}
    {before after : BST 0 n} (step : KeyRotationAt a b depth before after)
    (oldOwner newOwner : ℕ → ℕ)
    (oldOwners : Surface.Owners height before.depth oldOwner n)
    (newOwners : Surface.Owners height after.depth newOwner n)
    (oldTree newTree : BST 0 n)
    (oldCanonical : Surface.Canonical height (fun key => before.depth (oldOwner key)) oldTree)
    (newCanonical : Surface.Canonical height (fun key => after.depth (newOwner key)) newTree) :
    ∃ selected : Finset (External n), selected.card ≤ 10 ∧
      ∀ child, child ∉ selected →
        canonicalParent (Snapshot.ofTree after) newTree child =
          canonicalParent (Snapshot.ofTree before) oldTree child ∨
        ∃ oldParent newParent,
          canonicalParent (Snapshot.ofTree before) oldTree child = some oldParent ∧
          canonicalParent (Snapshot.ofTree after) newTree child = some newParent ∧
          oldParent.val = 2 * a + 1 ∧ newParent.val = 2 * b + 1 := by
  classical
  obtain ⟨support, bound, preserved⟩ := recanonicalization_parent_support
    step.toRotationAt oldOwner newOwner oldOwners newOwners oldTree newTree
    oldCanonical newCanonical
  let portA : Finset (External n) := Finset.univ.filter (fun child => child.val = 2 * a + 1)
  let portB : Finset (External n) := Finset.univ.filter (fun child => child.val = 2 * b + 1)
  have cardA : portA.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro x hx y hy
    apply Fin.ext
    exact (Finset.mem_filter.mp hx).2.trans (Finset.mem_filter.mp hy).2.symm
  have cardB : portB.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro x hx y hy
    apply Fin.ext
    exact (Finset.mem_filter.mp hx).2.trans (Finset.mem_filter.mp hy).2.symm
  refine ⟨support ∪ (portA ∪ portB), ?_, ?_⟩
  · have h₁ := Finset.card_union_le support (portA ∪ portB)
    have h₂ := Finset.card_union_le portA portB
    omega
  · intro child outside
    have notSupport : child ∉ support := fun h => outside (Finset.mem_union_left _ h)
    have notA : child.val ≠ 2 * a + 1 := by
      intro h
      exact outside (Finset.mem_union_right _ (Finset.mem_union_left _
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)))
    have notB : child.val ≠ 2 * b + 1 := by
      intro h
      exact outside (Finset.mem_union_right _ (Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)))
    rw [preserved child notSupport]
    exact ComparatorHeap.nonport_parent_changes step oldTree child notA notB

end GreedyMerge.Assembly

#print axioms GreedyMerge.Assembly.recanonicalization_parent_support
#print axioms GreedyMerge.Assembly.canonical_update_parent_relation

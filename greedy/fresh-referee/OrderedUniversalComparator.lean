import ComparatorOwnerDichotomy
import OrderedMacroBaseClosure

/-!
Universal fixed-refinement comparator administration. The literal geometric
case analysis is constructed from the actual rotation. Both possible
branches produce a complete ordered state with valid natural bases, and
all logical births are recorded explicitly rather than inferred from the
largest reserved identifier.
-/
namespace GreedyMerge.OrderedBlocks

open GreedyMerge.Primitives (Entry)
open GreedyMerge.BlockCoverage (Sound Complete)
open GreedyMerge.ComparatorOuter (RotationPlan rotationPlan)
open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Lazy.Canonical

/-- All spatial and numerical invariants needed by the next comparator
administration. Identifier/family freshness and chronological execution
histories are additional invariants, independent of this state predicate. -/
structure Ready {n : ℕ} (comparator tree : BST 0 n) (states : HeapSides n) : Prop where
  valid : ∀ owner side, Valid owner.val side (states owner side)
  sound : Sound (Snapshot.ofTree comparator) tree states
  complete : Complete (Snapshot.ofTree comparator) tree states
  persistent : PersistentGrowers states
  bases : ∀ owner side, BasesValid comparator.externalDepth owner.val (states owner side)

noncomputable def executeComparatorPlan {n a b depth : ℕ} {before after : BST 0 n}
    (profile : RotationCutProfile before after depth) (tree : BST 0 n)
    (plan : RotationPlan before after tree a b) (families ids : NameSupply n)
    (bulkFresh : Bool → ℕ) (paidNames : ℕ → PaidNames)
    (makeEntry : ℕ → External n → External n → Entry) (states : HeapSides n) : HeapSides n × ℕ :=
  match plan with
  | .quiet _ => administerRankOnly profile families ids states
  | .junction certificate =>
      administerJunction profile tree families ids certificate.node
        (certificate.node.owner (Snapshot.ofTree before)) (certificate.node.owner (Snapshot.ofTree after))
        bulkFresh paidNames makeEntry states

noncomputable def executeComparatorPlanIds {n a b depth : ℕ} {before after : BST 0 n}
    (profile : RotationCutProfile before after depth) (tree : BST 0 n)
    (plan : RotationPlan before after tree a b) (families ids : NameSupply n)
    (bulkFresh : Bool → ℕ) (paidNames : ℕ → PaidNames)
    (makeEntry : ℕ → External n → External n → Entry) (states : HeapSides n) : List ℕ :=
  match plan with
  | .quiet _ => prepareComparatorIds profile families ids [] ∅ states
  | .junction certificate =>
      administerJunctionIds profile tree families ids certificate.node
        (certificate.node.owner (Snapshot.ofTree before)) (certificate.node.owner (Snapshot.ofTree after))
        bulkFresh paidNames makeEntry states

theorem executeComparatorPlan_spec {n a b depth : ℕ} {before after : BST 0 n}
    (step : KeyRotationAt a b depth before after) (profile : RotationCutProfile before after depth)
    (tree : BST 0 n) (plan : RotationPlan before after tree a b) (families ids : NameSupply n)
    (bulkFresh : Bool → ℕ) (paidNames : ℕ → PaidNames)
    (makeEntry : ℕ → External n → External n → Entry)
    (key : ∀ stage record owner, (makeEntry stage record owner).key=record.val)
    (states : HeapSides n) (ready : Ready before tree states) :
    Ready after tree (executeComparatorPlan profile tree plan families ids bulkFresh paidNames makeEntry states).1 ∧
      (executeComparatorPlan profile tree plan families ids bulkFresh paidNames makeEntry states).2 ≤ 4*(depth+2)^2+23 := by
  have upper : ∀ owner side, UpperBase before.externalDepth (states owner side) :=
    fun owner side block member => (ready.bases owner side block member).2
  cases plan with
  | quiet parents =>
      obtain ⟨valid,sound,complete,persistent,budget⟩ := administerRankOnly_spec profile tree parents families ids states
        ready.valid ready.sound ready.complete ready.persistent
      exact ⟨⟨valid,sound,complete,persistent,
        administerRankOnly_bases profile tree parents families ids states ready.valid ready.sound upper⟩,
        le_trans budget (by omega)⟩
  | junction certificate =>
      obtain ⟨valid,sound,complete,persistent,budget⟩ := administerJunction_spec step profile tree certificate.node
        certificate.occurrence certificate.separated _ _ certificate.oldValue certificate.newValue rfl rfl certificate.different
        families ids bulkFresh paidNames makeEntry key states ready.valid ready.sound ready.complete ready.persistent
      exact ⟨⟨valid,sound,complete,persistent,
        administerJunction_bases step profile tree certificate.node certificate.occurrence certificate.separated _ _
          certificate.oldValue certificate.newValue rfl rfl certificate.different families ids bulkFresh paidNames makeEntry key
          states ready.valid ready.sound ready.complete ready.persistent upper⟩,budget⟩

theorem executeComparatorPlanIds_length {n a b depth : ℕ} {before after : BST 0 n}
    (profile : RotationCutProfile before after depth) (tree : BST 0 n)
    (plan : RotationPlan before after tree a b) (families ids : NameSupply n)
    (bulkFresh : Bool → ℕ) (paidNames : ℕ → PaidNames)
    (makeEntry : ℕ → External n → External n → Entry) (states : HeapSides n) :
    (executeComparatorPlanIds profile tree plan families ids bulkFresh paidNames makeEntry states).length =
      (executeComparatorPlan profile tree plan families ids bulkFresh paidNames makeEntry states).2 := by
  cases plan with
  | quiet => exact prepareComparatorIds_length profile families ids [] ∅ states
  | junction certificate => exact administerJunctionIds_length profile tree families ids certificate.node _ _ bulkFresh paidNames makeEntry states

theorem executeComparatorPlan_id_support {n a b depth : ℕ} {before after : BST 0 n}
    (profile : RotationCutProfile before after depth) (tree : BST 0 n)
    (plan : RotationPlan before after tree a b) (families ids : NameSupply n)
    (bulkFresh : Bool → ℕ) (paidNames : ℕ → PaidNames)
    (makeEntry : ℕ → External n → External n → Entry) (states : HeapSides n) :
    SupportsIds states (executeComparatorPlan profile tree plan families ids bulkFresh paidNames makeEntry states).1
      (executeComparatorPlanIds profile tree plan families ids bulkFresh paidNames makeEntry states) := by
  cases plan with
  | quiet => exact administerRankOnly_id_support profile families ids states
  | junction certificate => exact administerJunction_id_support profile tree families ids certificate.node _ _ bulkFresh paidNames makeEntry states

/-- A total constructor for every actual comparator rotation at any depth. -/
noncomputable def administerComparator {n a b depth : ℕ} {before after : BST 0 n}
    (step : KeyRotationAt a b depth before after) (profile : RotationCutProfile before after depth)
    (tree : BST 0 n) (families ids : NameSupply n) (bulkFresh : Bool → ℕ)
    (paidNames : ℕ → PaidNames) (makeEntry : ℕ → External n → External n → Entry)
    (states : HeapSides n) : HeapSides n × ℕ :=
  executeComparatorPlan profile tree (rotationPlan step tree) families ids bulkFresh paidNames makeEntry states

theorem administerComparator_spec {n a b depth : ℕ} {before after : BST 0 n}
    (step : KeyRotationAt a b depth before after) (profile : RotationCutProfile before after depth)
    (tree : BST 0 n) (families ids : NameSupply n) (bulkFresh : Bool → ℕ)
    (paidNames : ℕ → PaidNames) (makeEntry : ℕ → External n → External n → Entry)
    (key : ∀ stage record owner, (makeEntry stage record owner).key=record.val)
    (states : HeapSides n) (ready : Ready before tree states) :
    Ready after tree (administerComparator step profile tree families ids bulkFresh paidNames makeEntry states).1 ∧
      (administerComparator step profile tree families ids bulkFresh paidNames makeEntry states).2 ≤ 4*(depth+2)^2+23 :=
  executeComparatorPlan_spec step profile tree (rotationPlan step tree) families ids bulkFresh paidNames makeEntry key states ready

/-- Concrete key and rank-cut data, chosen from an arbitrary contextual
rotation; neither is an additional caller premise. -/
structure ComparatorInput {n depth : ℕ} (before after : BST 0 n) where
  demoted : ℕ
  promoted : ℕ
  step : KeyRotationAt demoted promoted depth before after
  profile : RotationCutProfile before after depth

noncomputable def comparatorInput {n depth : ℕ} {before after : BST 0 n}
    (rotation : RotationAt depth before after) : ComparatorInput (depth:=depth) before after := by
  classical
  let a := Classical.choose (exists_keyRotationAt rotation)
  let b := Classical.choose (Classical.choose_spec (exists_keyRotationAt rotation))
  exact ⟨a,b,Classical.choose_spec (Classical.choose_spec (exists_keyRotationAt rotation)),
    Classical.choice rotation.exists_cutProfile⟩

noncomputable def administerActualComparator {n depth : ℕ} {before after : BST 0 n}
    (rotation : RotationAt depth before after) (tree : BST 0 n)
    (families ids : NameSupply n) (bulkFresh : Bool → ℕ)
    (paidNames : ℕ → PaidNames) (makeEntry : ℕ → External n → External n → Entry)
    (states : HeapSides n) : HeapSides n × ℕ :=
  let input := comparatorInput rotation
  administerComparator input.step input.profile tree families ids bulkFresh paidNames makeEntry states

theorem administerActualComparator_spec {n depth : ℕ} {before after : BST 0 n}
    (rotation : RotationAt depth before after) (tree : BST 0 n)
    (families ids : NameSupply n) (bulkFresh : Bool → ℕ)
    (paidNames : ℕ → PaidNames) (makeEntry : ℕ → External n → External n → Entry)
    (key : ∀ stage record owner, (makeEntry stage record owner).key=record.val)
    (states : HeapSides n) (ready : Ready before tree states) :
    Ready after tree (administerActualComparator rotation tree families ids bulkFresh paidNames makeEntry states).1 ∧
      (administerActualComparator rotation tree families ids bulkFresh paidNames makeEntry states).2 ≤ 4*(depth+2)^2+23 :=
  administerComparator_spec (comparatorInput rotation).step (comparatorInput rotation).profile tree
    families ids bulkFresh paidNames makeEntry key states ready

#print axioms executeComparatorPlan_spec
#print axioms executeComparatorPlanIds_length
#print axioms executeComparatorPlan_id_support
#print axioms administerComparator_spec
#print axioms administerActualComparator_spec

end GreedyMerge.OrderedBlocks

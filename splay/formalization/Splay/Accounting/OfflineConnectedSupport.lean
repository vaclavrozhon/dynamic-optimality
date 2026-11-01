import Splay.Accounting.OfflineRootStandardEquivalence
import Splay.Accounting.OfflineStructuralExecutionNormalForm

namespace Splay.Accounting.OfflineConnectedSupport

open Splay.Tree.BST
open Splay.Assumptions.NormalForm

abbrev BST := Splay.Tree.BST

/--
An ancestor-closed prefix of an indexed BST.

`none` selects no value node from a subtree.  `node` selects the subtree root
and independently selects ancestor-closed prefixes of its two children.
Consequently every nonempty value selected by a `RootPrefix` is connected to
the root through selected value nodes.  The representation is proof-relevant:
unselected child subtrees remain present as explicit hanging subtrees.
-/
inductive RootPrefix :
    {lower upper : ℕ} → (tree : BST lower upper) → Type
  | none {lower upper : ℕ} (tree : BST lower upper) :
      RootPrefix tree
  | node {lower root upper : ℕ}
      {left : BST lower root} {right : BST (root + 1) upper}
      (leftPrefix : RootPrefix left)
      (rightPrefix : RootPrefix right) :
      RootPrefix (.node left right)

namespace RootPrefix

/-- Number of selected value nodes in an ancestor-closed root prefix. -/
def card {lower upper : ℕ} {tree : BST lower upper} :
    RootPrefix tree → ℕ
  | .none _ => 0
  | .node left right => left.card + 1 + right.card

/-- The prefix containing every value node of a tree. -/
def full {lower upper : ℕ} :
    (tree : BST lower upper) → RootPrefix tree
  | .empty boundary => .none (.empty boundary)
  | .node left right => .node (full left) (full right)

/-- The full prefix contains exactly all value nodes. -/
@[simp]
theorem card_full {lower upper : ℕ} (tree : BST lower upper) :
    (full tree).card = tree.size := by
  induction tree with
  | empty =>
      rfl
  | node left right ihLeft ihRight =>
      simp [full, card, Splay.Tree.BST.size, ihLeft, ihRight]

end RootPrefix

/--
One rotation whose two rotated value nodes belong to a transported
root-connected prefix.

The before- and after-prefixes select exactly the same value nodes.  At a root
rotation, the three child prefixes are merely reassociated.  Context
constructors transport the unchanged prefix on the sibling subtree.  Thus an
unselected hanging subtree is never internally modified.
-/
inductive SupportedRotation :
    {depth lower upper : ℕ} →
      {before after : BST lower upper} →
    RotationAt depth before after →
    RootPrefix before → RootPrefix after → Prop
  | rootRight {lower promoted demoted upper : ℕ}
      (a : BST lower promoted)
      (b : BST (promoted + 1) demoted)
      (c : BST (demoted + 1) upper)
      (aPrefix : RootPrefix a)
      (bPrefix : RootPrefix b)
      (cPrefix : RootPrefix c) :
      SupportedRotation
        (.root (.right a b c))
        (.node (.node aPrefix bPrefix) cPrefix)
        (.node aPrefix (.node bPrefix cPrefix))
  | rootLeft {lower promoted demoted upper : ℕ}
      (a : BST lower promoted)
      (b : BST (promoted + 1) demoted)
      (c : BST (demoted + 1) upper)
      (aPrefix : RootPrefix a)
      (bPrefix : RootPrefix b)
      (cPrefix : RootPrefix c) :
      SupportedRotation
        (.root (.left a b c))
        (.node aPrefix (.node bPrefix cPrefix))
        (.node (.node aPrefix bPrefix) cPrefix)
  | leftContext {depth lower root upper : ℕ}
      {before after : BST lower root}
      {beforePrefix : RootPrefix before}
      {afterPrefix : RootPrefix after}
      (rotation : RotationAt depth before after)
      (supported :
        SupportedRotation rotation beforePrefix afterPrefix)
      (right : BST (root + 1) upper)
      (rightPrefix : RootPrefix right) :
      SupportedRotation
        (.leftContext rotation right)
        (.node beforePrefix rightPrefix)
        (.node afterPrefix rightPrefix)
  | rightContext {depth lower root upper : ℕ}
      (left : BST lower root)
      (leftPrefix : RootPrefix left)
      {before after : BST (root + 1) upper}
      {beforePrefix : RootPrefix before}
      {afterPrefix : RootPrefix after}
      (rotation : RotationAt depth before after)
      (supported :
        SupportedRotation rotation beforePrefix afterPrefix) :
      SupportedRotation
        (.rightContext left rotation)
        (.node leftPrefix beforePrefix)
        (.node leftPrefix afterPrefix)

namespace SupportedRotation

/-- A supported rotation preserves the number of selected support nodes. -/
theorem card_eq
    {depth lower upper : ℕ}
    {before after : BST lower upper}
    {rotation : RotationAt depth before after}
    {beforePrefix : RootPrefix before}
    {afterPrefix : RootPrefix after}
    (supported :
      SupportedRotation rotation beforePrefix afterPrefix) :
    beforePrefix.card = afterPrefix.card := by
  induction supported with
  | rootRight =>
      simp only [RootPrefix.card]
      omega
  | rootLeft =>
      simp only [RootPrefix.card]
      omega
  | leftContext rotation supported right rightPrefix ih =>
      simp [RootPrefix.card, ih]
  | rightContext left leftPrefix rotation supported ih =>
      simp [RootPrefix.card, ih]

/--
Supporting a rotation at depth `d` needs at least `d + 2` selected nodes:
the root-to-rotation path and both endpoints of the rotated edge.
-/
theorem depth_add_two_le_card
    {depth lower upper : ℕ}
    {before after : BST lower upper}
    {rotation : RotationAt depth before after}
    {beforePrefix : RootPrefix before}
    {afterPrefix : RootPrefix after}
    (supported :
      SupportedRotation rotation beforePrefix afterPrefix) :
    depth + 2 ≤ beforePrefix.card := by
  induction supported with
  | rootRight =>
      simp only [RootPrefix.card]
      omega
  | rootLeft =>
      simp only [RootPrefix.card]
      omega
  | leftContext rotation supported right rightPrefix ih =>
      simp only [RootPrefix.card]
      omega
  | rightContext left leftPrefix rotation supported ih =>
      simp only [RootPrefix.card]
      omega

end SupportedRotation

namespace RotationAt

/-- Every ordinary rotation is supported by the full root prefix. -/
theorem supportedByFull
    {depth lower upper : ℕ}
    {before after : BST lower upper}
    (rotation : RotationAt depth before after) :
    SupportedRotation rotation
      (RootPrefix.full before) (RootPrefix.full after) := by
  induction rotation with
  | root rootRotation =>
      cases rootRotation with
      | right a b c =>
          exact .rootRight a b c
            (RootPrefix.full a)
            (RootPrefix.full b)
            (RootPrefix.full c)
      | left a b c =>
          exact .rootLeft a b c
            (RootPrefix.full a)
            (RootPrefix.full b)
            (RootPrefix.full c)
  | leftContext rotation right ih =>
      exact
        .leftContext rotation ih right (RootPrefix.full right)
  | rightContext left rotation ih =>
      exact
        .rightContext left (RootPrefix.full left) rotation ih

end RotationAt

/-- A finite rotation execution transported inside one root-connected prefix. -/
inductive SupportedRotationExecution :
    ℕ → {lower upper : ℕ} →
      {before after : BST lower upper} →
      RootPrefix before → RootPrefix after → Prop
  | refl {lower upper : ℕ} {tree : BST lower upper}
      (selectedPrefix : RootPrefix tree) :
      SupportedRotationExecution 0 selectedPrefix selectedPrefix
  | step {length depth lower upper : ℕ}
      {before middle after : BST lower upper}
      {beforePrefix : RootPrefix before}
      {middlePrefix : RootPrefix middle}
      {afterPrefix : RootPrefix after}
      (rotation : RotationAt depth before middle)
      (supported :
        SupportedRotation rotation beforePrefix middlePrefix)
      (tail :
        SupportedRotationExecution length
          middlePrefix afterPrefix) :
      SupportedRotationExecution length.succ
        beforePrefix afterPrefix

namespace SupportedRotationExecution

/-- Forgetting support recovers the underlying ordinary rotation execution. -/
theorem toRotationExecution
    {length lower upper : ℕ}
    {before after : BST lower upper}
    {beforePrefix : RootPrefix before}
    {afterPrefix : RootPrefix after}
    (execution :
      SupportedRotationExecution length beforePrefix afterPrefix) :
    RotationExecution length before after := by
  induction execution with
  | refl selectedPrefix =>
      exact .refl
  | step rotation supported tail ih =>
      exact .step rotation ih

/-- A supported execution transports a support of unchanged cardinality. -/
theorem card_eq
    {length lower upper : ℕ}
    {before after : BST lower upper}
    {beforePrefix : RootPrefix before}
    {afterPrefix : RootPrefix after}
    (execution :
      SupportedRotationExecution length beforePrefix afterPrefix) :
    beforePrefix.card = afterPrefix.card := by
  induction execution with
  | refl =>
      rfl
  | step rotation supported tail ih =>
      exact supported.card_eq.trans ih

end SupportedRotationExecution

namespace RotationExecution

/-- Any rotation execution is supported by selecting the entire tree. -/
theorem supportedByFull
    {length lower upper : ℕ}
    {before after : BST lower upper}
    (execution : RotationExecution length before after) :
    SupportedRotationExecution length
      (RootPrefix.full before) (RootPrefix.full after) := by
  induction execution with
  | refl =>
      exact .refl (RootPrefix.full _)
  | step rotation tail ih =>
      exact .step rotation (RotationAt.supportedByFull rotation) ih

end RotationExecution

/--
An offline execution whose work at each request is confined to one
root-connected prefix.

The two indices record ordinary rotations and, separately, the sum of support
cardinalities charged once per served request.  Keeping these quantities
separate exposes exactly the premise used in Appendix C: the changed region is
root-connected and its size is charged.
-/
inductive ConnectedExecution {n : ℕ} :
    List (Fin n) → BST 0 n → BST 0 n → ℕ → ℕ → Prop
  | done (tree : BST 0 n) :
      ConnectedExecution [] tree tree 0 0
  | next {access : Fin n} {accesses : List (Fin n)}
      {before served after : BST 0 n}
      {beforePrefix : RootPrefix before}
      {servedPrefix : RootPrefix served}
      {prefixRotations tailRotations tailSupportCharge : ℕ}
      (supportedPrefix :
        SupportedRotationExecution prefixRotations
          beforePrefix servedPrefix)
      (supportNonempty : 0 < beforePrefix.card)
      (root : served.HasRoot access.val)
      (tail :
        ConnectedExecution accesses served after
          tailRotations tailSupportCharge) :
      ConnectedExecution (access :: accesses) before after
        (prefixRotations + tailRotations)
        (beforePrefix.card + tailSupportCharge)

namespace ConnectedExecution

/-- Forgetting the support certificates yields a genuine root execution. -/
theorem toOfflineExecution
    {n rotations supportCharge : ℕ}
    {accesses : List (Fin n)}
    {before after : BST 0 n}
    (execution :
      ConnectedExecution accesses before after
        rotations supportCharge) :
    Splay.Accounting.OfflineOptimum.Execution
      accesses before after rotations := by
  induction execution with
  | done tree =>
      exact Splay.Accounting.OfflineOptimum.Execution.done tree
  | next supportedPrefix supportNonempty root tail ih =>
      exact .next supportedPrefix.toRotationExecution root ih

end ConnectedExecution

namespace ConnectedExecution

/--
Selecting the entire tree at every request turns any arbitrary-rotation
execution into a connected-support execution.  The exact support charge is
`number of requests * n`; this is a finite but non-uniform fallback, not the
constant-factor Appendix-C normalization.
-/
theorem toFullConnectedExecution
    {n rotations : ℕ}
    {accesses : List (Fin n)}
    {before after : BST 0 n}
    (execution :
      Splay.Accounting.OfflineOptimum.Execution
        accesses before after rotations) :
    ConnectedExecution accesses before after rotations
      (accesses.length * n) := by
  induction execution with
  | done tree =>
      simpa using (ConnectedExecution.done tree)
  | @next access accesses before served after
      prefixRotations tailRotations prefixExecution root tail ih =>
      have supportNonempty :
          0 < (RootPrefix.full before).card := by
        rw [RootPrefix.card_full, before.size_eq_upper]
        exact Nat.zero_lt_of_lt access.isLt
      have built :
          ConnectedExecution (access :: accesses) before after
            (prefixRotations + tailRotations)
            ((RootPrefix.full before).card +
              accesses.length * n) :=
        ConnectedExecution.next
          (RotationExecution.supportedByFull prefixExecution)
          supportNonempty root ih
      simpa
        [RootPrefix.card_full, before.size_eq_upper,
          List.length_cons, Nat.succ_mul, Nat.add_comm]
        using built

end ConnectedExecution

/-- Costs attained by connected-support executions. -/
def FeasibleConnectedCost {n : ℕ}
    (accesses : List (Fin n)) (cost : ℕ) : Prop :=
  ∃ (initial final : BST 0 n)
      (rotations supportCharge : ℕ),
    ConnectedExecution accesses initial final
      rotations supportCharge ∧
    cost = accesses.length + rotations + supportCharge

/-- Every request sequence has a finite connected-support execution. -/
theorem exists_feasibleConnectedCost
    {n : ℕ} (accesses : List (Fin n)) :
    ∃ cost, FeasibleConnectedCost accesses cost := by
  obtain ⟨initial, final, rotations, execution, costEq⟩ :=
    Splay.Accounting.OfflineOptimum.exists_optimalExecution_eq accesses
  refine
    ⟨accesses.length + rotations + accesses.length * n,
      initial, final, rotations, accesses.length * n,
      ConnectedExecution.toFullConnectedExecution execution, rfl⟩

/-- The attained optimum of the connected-support execution interface. -/
noncomputable def connectedOptCost
    {n : ℕ} (accesses : List (Fin n)) : ℕ := by
  classical
  exact Nat.find (exists_feasibleConnectedCost accesses)

/-- The connected-support optimum is attained. -/
theorem connectedOptCost_feasible
    {n : ℕ} (accesses : List (Fin n)) :
    FeasibleConnectedCost accesses (connectedOptCost accesses) := by
  classical
  exact Nat.find_spec (exists_feasibleConnectedCost accesses)

/-- The connected-support optimum is below every feasible connected cost. -/
theorem connectedOptCost_le
    {n cost : ℕ} {accesses : List (Fin n)}
    (feasible : FeasibleConnectedCost accesses cost) :
    connectedOptCost accesses ≤ cost := by
  classical
  simpa [connectedOptCost] using
    Nat.find_min' (exists_feasibleConnectedCost accesses) feasible

/--
Forgetting support proves that the arbitrary-rotation root optimum is no
larger than the connected-support optimum.
-/
theorem offlineOptCost_le_connectedOptCost
    {n : ℕ} (accesses : List (Fin n)) :
    Splay.Accounting.OfflineOptimum.offlineOptCost accesses ≤
      connectedOptCost accesses := by
  obtain
    ⟨initial, final, rotations, supportCharge,
      connected, costEq⟩ :=
    connectedOptCost_feasible accesses
  calc
    Splay.Accounting.OfflineOptimum.offlineOptCost accesses ≤
        accesses.length + rotations :=
      Splay.Accounting.OfflineOptimum.offlineOptCost_le_ofExecution
        connected.toOfflineExecution
    _ ≤ accesses.length + rotations + supportCharge :=
      Nat.le_add_right _ _
    _ = connectedOptCost accesses :=
      costEq.symm

/--
The full-tree fallback gives an explicit finite comparison, with the exact
non-uniform additive support charge `m*n`.
-/
theorem connectedOptCost_le_offlineOptCost_add_fullSupport
    {n : ℕ} (accesses : List (Fin n)) :
    connectedOptCost accesses ≤
      Splay.Accounting.OfflineOptimum.offlineOptCost accesses +
        accesses.length * n := by
  obtain ⟨initial, final, rotations, execution, costEq⟩ :=
    Splay.Accounting.OfflineOptimum.exists_optimalExecution_eq accesses
  have feasible :
      FeasibleConnectedCost accesses
        (accesses.length + rotations + accesses.length * n) :=
    ⟨initial, final, rotations, accesses.length * n,
      ConnectedExecution.toFullConnectedExecution execution, rfl⟩
  calc
    connectedOptCost accesses ≤
        accesses.length + rotations + accesses.length * n :=
      connectedOptCost_le feasible
    _ =
        Splay.Accounting.OfflineOptimum.offlineOptCost accesses +
          accesses.length * n := by
      rw [costEq]

/--
Cost-level statement of uniform connected-support normalization, proved with
multiplier two in `OfflineConnectedNormalization`.
-/
def UniformConnectedSupportNormalization : Prop :=
  ∃ multiplier : ℕ,
    ∀ (n : ℕ) (accesses : List (Fin n)),
      connectedOptCost accesses ≤
        multiplier *
          Splay.Accounting.OfflineOptimum.offlineOptCost accesses

/--
The same normalization stated constructively on an attained optimal
arbitrary-rotation execution.
-/
def UniformOptimalExecutionConnectedNormalizer : Prop :=
  ∃ multiplier : ℕ,
    ∀ (n : ℕ) (accesses : List (Fin n))
      (before after : BST 0 n) (rotations : ℕ),
      Splay.Accounting.OfflineOptimum.Execution
          accesses before after rotations →
      Splay.Accounting.OfflineOptimum.offlineOptCost accesses =
          accesses.length + rotations →
      ∃ (targetBefore targetAfter : BST 0 n)
          (targetRotations supportCharge : ℕ),
        ConnectedExecution accesses targetBefore targetAfter
          targetRotations supportCharge ∧
        accesses.length + targetRotations + supportCharge ≤
          multiplier * (accesses.length + rotations)

/--
There is no hidden attainment or presentation gap: the cost-level and
execution-level connected-support normalization statements are equivalent.
-/
theorem
    uniformOptimalExecutionConnectedNormalizer_iff_costNormalization :
    UniformOptimalExecutionConnectedNormalizer ↔
      UniformConnectedSupportNormalization := by
  constructor
  · rintro ⟨multiplier, normalize⟩
    refine ⟨multiplier, ?_⟩
    intro n accesses
    obtain ⟨before, after, rotations, execution, optimumEq⟩ :=
      Splay.Accounting.OfflineOptimum.exists_optimalExecution_eq accesses
    obtain
      ⟨targetBefore, targetAfter, targetRotations, supportCharge,
        connected, targetBound⟩ :=
      normalize n accesses before after rotations execution optimumEq
    have feasible :
        FeasibleConnectedCost accesses
          (accesses.length + targetRotations + supportCharge) :=
      ⟨targetBefore, targetAfter, targetRotations, supportCharge,
        connected, rfl⟩
    calc
      connectedOptCost accesses ≤
          accesses.length + targetRotations + supportCharge :=
        connectedOptCost_le feasible
      _ ≤ multiplier * (accesses.length + rotations) :=
        targetBound
      _ =
          multiplier *
            Splay.Accounting.OfflineOptimum.offlineOptCost accesses := by
        rw [optimumEq]
  · rintro ⟨multiplier, normalize⟩
    refine ⟨multiplier, ?_⟩
    intro n accesses before after rotations execution optimumEq
    obtain
      ⟨targetBefore, targetAfter, targetRotations, supportCharge,
        connected, connectedCostEq⟩ :=
      connectedOptCost_feasible accesses
    refine
      ⟨targetBefore, targetAfter, targetRotations, supportCharge,
        connected, ?_⟩
    calc
      accesses.length + targetRotations + supportCharge =
          connectedOptCost accesses :=
        connectedCostEq.symm
      _ ≤
          multiplier *
            Splay.Accounting.OfflineOptimum.offlineOptCost accesses :=
        normalize n accesses
      _ = multiplier * (accesses.length + rotations) := by
        rw [optimumEq]

/--
The downstream structural simulation obligation once connected support is
available.

This interface deliberately starts from `ConnectedExecution`, so it contains
the Bose logarithmic-depth representation, Brodal--Rysgaard rib replacement,
and Cleary--Taback restricted-rotation work, but no arbitrary-rotation to
connected-support reduction.
-/
def UniformConnectedExecutionStructuralSimulator : Prop :=
  ∃ bounds : StructuralBounds,
    ∀ (n : ℕ), 0 < n →
      ∀ (accesses : List (Fin n))
        (before after : BST 0 n)
        (rotations supportCharge : ℕ),
        ConnectedExecution accesses before after
            rotations supportCharge →
          ∃ target : ComparisonTrace n accesses,
            IsStructurallyNormal bounds target ∧
              target.cost ≤
                bounds.costMultiplier *
                  (accesses.length + rotations + supportCharge)

/--
The connected-support normalization and the downstream structural simulator
compose to the exact optimal-execution structural normalizer consumed by the
rest of the formalization.

The `+1` in the composed multiplier only supplies the positivity field when a
putative connected normalizer chooses multiplier zero.
-/
theorem connectedNormalization_and_structuralSimulator_imply_normalForm
    (connectedNormalizer :
      UniformOptimalExecutionConnectedNormalizer)
    (structuralSimulator :
      UniformConnectedExecutionStructuralSimulator) :
    Splay.Accounting.OfflineNormalForm.UniformOptimalExecutionStructuralNormalizer := by
  rcases connectedNormalizer with
    ⟨connectedMultiplier, normalizeConnected⟩
  rcases structuralSimulator with
    ⟨structuralBounds, simulateStructural⟩
  let composedBounds : StructuralBounds :=
    { structuralBounds with
      costMultiplier :=
        structuralBounds.costMultiplier *
          (connectedMultiplier + 1)
      costMultiplier_pos :=
        Nat.mul_pos structuralBounds.costMultiplier_pos
          (Nat.succ_pos connectedMultiplier) }
  refine ⟨composedBounds, ?_⟩
  intro n n_pos accesses before after rotations execution optimumEq
  obtain
    ⟨connectedBefore, connectedAfter,
      connectedRotations, supportCharge,
      connected, connectedCostBound⟩ :=
    normalizeConnected n accesses before after rotations
      execution optimumEq
  obtain ⟨target, structural, structuralCostBound⟩ :=
    simulateStructural n n_pos accesses
      connectedBefore connectedAfter
      connectedRotations supportCharge connected
  refine ⟨target, ?_, ?_⟩
  · exact
      { normal :=
          { height_le := structural.normal.height_le
            rotationDepth_le :=
              structural.normal.rotationDepth_le }
        relevantNeighborDepth_le :=
          structural.relevantNeighborDepth_le }
  · calc
      target.cost ≤
          structuralBounds.costMultiplier *
            (accesses.length + connectedRotations + supportCharge) :=
        structuralCostBound
      _ ≤
          structuralBounds.costMultiplier *
            (connectedMultiplier *
              (accesses.length + rotations)) :=
        Nat.mul_le_mul_left _ connectedCostBound
      _ =
          (structuralBounds.costMultiplier * connectedMultiplier) *
            (accesses.length + rotations) := by
        simp [Nat.mul_assoc]
      _ ≤
          (structuralBounds.costMultiplier *
              (connectedMultiplier + 1)) *
            (accesses.length + rotations) := by
        exact
          Nat.mul_le_mul_right _
            (Nat.mul_le_mul_left _
              (Nat.le_succ connectedMultiplier))
      _ =
          composedBounds.costMultiplier *
            (accesses.length + rotations) := rfl

/--
At every requested budget there is a rooted one-rotation execution whose
exact rotation cannot be represented inside a support of that cardinality.

This is a quantitative form of the arbitrary-depth obstruction: it applies to
preserving the supplied rotation, not to replacing an optimal execution by a
different one.
-/
theorem exists_rootedRotation_requiring_larger_support
    (budget : ℕ) :
    ∃ (n : ℕ) (access : Fin n) (before after : BST 0 n)
        (rotation : RotationAt budget.succ before after),
      before.HasRoot access.val ∧
        after.HasRoot access.val ∧
        Splay.Accounting.OfflineOptimum.Execution
          [access] before after 1 ∧
        ∀ (beforePrefix : RootPrefix before)
          (afterPrefix : RootPrefix after),
          SupportedRotation rotation beforePrefix afterPrefix →
            budget < beforePrefix.card := by
  obtain
    ⟨n, n_pos, access, before, after,
      rotation, beforeRoot, afterRoot, execution⟩ :=
    Splay.Accounting.OfflineOptimum.exists_rootedAccessExecution_with_unboundedPreparationDepth
      budget
  refine
    ⟨n, access, before, after, rotation,
      beforeRoot, afterRoot, execution, ?_⟩
  intro beforePrefix afterPrefix supported
  have depthBound := supported.depth_add_two_le_card
  omega

/--
No universal constant-factor conversion can preserve every individual
arbitrary-depth rotation and merely add a connected support around it.

Both source executions in the quantified family cost two
(`one request + one rotation`).  The false interface below would keep that
same rotation and charge `one request + one rotation + support cardinality`.
The preceding depth lower bound makes the ratio unbounded.

This does not refute `UniformConnectedSupportNormalization`, which may choose
a different execution and is required only at the global optimum.
-/
theorem no_uniform_phasewise_sameRotation_simulation :
    ¬ ∃ multiplier : ℕ,
      ∀ (n : ℕ) (access : Fin n)
        (before after : BST 0 n) (depth : ℕ)
        (rotation : RotationAt depth before after),
        before.HasRoot access.val →
        after.HasRoot access.val →
        ∃ (beforePrefix : RootPrefix before)
          (afterPrefix : RootPrefix after),
          SupportedRotation rotation beforePrefix afterPrefix ∧
            1 + 1 + beforePrefix.card ≤ multiplier * (1 + 1) := by
  rintro ⟨multiplier, simulate⟩
  obtain
    ⟨n, access, before, after, rotation,
      beforeRoot, afterRoot, execution, supportLarge⟩ :=
    exists_rootedRotation_requiring_larger_support (2 * multiplier)
  obtain
    ⟨beforePrefix, afterPrefix, supported, targetBound⟩ :=
    simulate n access before after (2 * multiplier).succ
      rotation beforeRoot afterRoot
  have large := supportLarge beforePrefix afterPrefix supported
  omega

end Splay.Accounting.OfflineConnectedSupport

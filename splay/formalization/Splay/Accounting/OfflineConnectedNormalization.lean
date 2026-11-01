import Splay.Accounting.OfflineConnectedSupport

/-!
# Postponing rotations outside a connected root service

We reuse the existing selected-prefix representation instead of constructing
an interaction graph. Traversing a rotation sequence backwards either pushes
an outside rotation to the deferred suffix, or includes the rotation after
enlarging the selected prefix by at most one node. Starting from the final
singleton root gives `support.card ≤ keptRotations + 1`.

`RotationExecution.factor_root` keeps the exact old endpoint after the
deferred suffix. `exists_connectedReordered` prepends this suffix to the next
request, discarding it only after the last request. Summing the local support
bounds proves the factor-two comparison of the two attained optima.
-/

namespace Splay.Accounting.OfflineConnectedSupport

open Splay.Tree.BST

namespace RootPrefix

/-- Enlarging a selected prefix without changing its underlying tree. -/
inductive Refines : {lower upper : ℕ} → {tree : BST lower upper} →
    RootPrefix tree → RootPrefix tree → Prop
  | none {lower upper : ℕ} {tree : BST lower upper} (selected : RootPrefix tree) :
      Refines (.none tree) selected
  | node {lower root upper : ℕ}
      {left : BST lower root} {right : BST (root + 1) upper}
      {a a' : RootPrefix left} {b b' : RootPrefix right}
      (left : Refines a a') (right : Refines b b') :
      Refines (.node a b) (.node a' b')

theorem Refines.refl {lower upper : ℕ} {tree : BST lower upper}
    (selected : RootPrefix tree) : Refines selected selected := by
  induction selected with
  | none => exact .none _
  | node a b ihA ihB => exact .node ihA ihB

theorem Refines.card_le {lower upper : ℕ} {tree : BST lower upper}
    {a b : RootPrefix tree} (refines : Refines a b) : a.card ≤ b.card := by
  induction refines with
  | none => simp [card]
  | node left right ihL ihR => simp only [card]; omega

end RootPrefix

namespace SupportedRotation

/-- A supported step remains supported when more hanging nodes are selected. -/
theorem refine
    {depth lower upper : ℕ} {before after : BST lower upper}
    {rotation : RotationAt depth before after}
    {a : RootPrefix before} {b : RootPrefix after}
    (supported : SupportedRotation rotation a b)
    {a' : RootPrefix before} (larger : a.Refines a') :
    ∃ b' : RootPrefix after, b.Refines b' ∧ SupportedRotation rotation a' b' := by
  induction supported with
  | rootRight x y z px py pz =>
      cases larger with
      | node left right =>
          cases left with
          | node first second =>
              exact ⟨_, .node first (.node second right), .rootRight _ _ _ _ _ _⟩
  | rootLeft x y z px py pz =>
      cases larger with
      | node left right =>
          cases right with
          | node second third =>
              exact ⟨_, .node (.node left second) third, .rootLeft _ _ _ _ _ _⟩
  | leftContext rotation supported right rightPrefix ih =>
      cases larger with
      | node left rightRefines =>
          obtain ⟨newPrefix, refined, step⟩ := ih left
          exact ⟨_, .node refined rightRefines, .leftContext rotation step _ _⟩
  | rightContext left leftPrefix rotation supported ih =>
      cases larger with
      | node leftRefines right =>
          obtain ⟨newPrefix, refined, step⟩ := ih right
          exact ⟨_, .node leftRefines refined, .rightContext _ _ rotation step⟩

end SupportedRotation

namespace SupportedRotationExecution

theorem refine {length lower upper : ℕ} {before after : BST lower upper}
    {a : RootPrefix before} {b : RootPrefix after}
    (execution : SupportedRotationExecution length a b)
    {a' : RootPrefix before} (larger : a.Refines a') :
    ∃ b' : RootPrefix after, b.Refines b' ∧
      SupportedRotationExecution length a' b' := by
  induction execution with
  | refl selected => exact ⟨a', larger, .refl _⟩
  | step rotation supported tail ih =>
      obtain ⟨middle, middleRefines, first⟩ := supported.refine larger
      obtain ⟨last, lastRefines, rest⟩ := ih middleRefines
      exact ⟨last, lastRefines, .step rotation first rest⟩

end SupportedRotationExecution

/-- One rotation entirely within an unselected hanging subtree. -/
inductive OutsideRotation : {lower upper : ℕ} →
    {before after : BST lower upper} → RootPrefix before → RootPrefix after → Prop
  | hidden {depth lower upper : ℕ} {before after : BST lower upper}
      (rotation : RotationAt depth before after) :
      OutsideRotation (.none before) (.none after)
  | left {lower root upper : ℕ} {before after : BST lower root}
      {a : RootPrefix before} {b : RootPrefix after}
      (rotation : OutsideRotation a b)
      {right : BST (root + 1) upper} (rightPrefix : RootPrefix right) :
      OutsideRotation (.node a rightPrefix) (.node b rightPrefix)
  | right {lower root upper : ℕ} {before after : BST (root + 1) upper}
      {a : RootPrefix before} {b : RootPrefix after}
      {left : BST lower root} (leftPrefix : RootPrefix left)
      (rotation : OutsideRotation a b) :
      OutsideRotation (.node leftPrefix a) (.node leftPrefix b)

namespace OutsideRotation

theorem card_eq {lower upper : ℕ} {before after : BST lower upper}
    {a : RootPrefix before} {b : RootPrefix after}
    (rotation : OutsideRotation a b) : a.card = b.card := by
  induction rotation with
  | hidden => rfl
  | left rotation right ih => simp [RootPrefix.card, ih]
  | right left rotation ih => simp [RootPrefix.card, ih]

theorem exists_rotation {lower upper : ℕ} {before after : BST lower upper}
    {a : RootPrefix before} {b : RootPrefix after}
    (outside : OutsideRotation a b) : ∃ depth, RotationAt depth before after := by
  induction outside with
  | hidden rotation => exact ⟨_, rotation⟩
  | left outside right ih =>
      obtain ⟨depth, rotation⟩ := ih
      exact ⟨_, .leftContext rotation _⟩
  | right left outside ih =>
      obtain ⟨depth, rotation⟩ := ih
      exact ⟨_, .rightContext _ rotation⟩

theorem root_before {lower upper key : ℕ} {before after : BST lower upper}
    {a : RootPrefix before} {b : RootPrefix after}
    (outside : OutsideRotation a b) (positive : 0 < b.card)
    (root : after.HasRoot key) : before.HasRoot key := by
  cases outside with
  | hidden => simp [RootPrefix.card] at positive
  | left =>
      obtain ⟨_, _, equal⟩ := root
      cases equal
      exact ⟨_, _, rfl⟩
  | right =>
      obtain ⟨_, _, equal⟩ := root
      cases equal
      exact ⟨_, _, rfl⟩

end OutsideRotation

namespace SupportedRotation

theorem toExecution {depth lower upper : ℕ} {before after : BST lower upper}
    {rotation : RotationAt depth before after}
    {a : RootPrefix before} {b : RootPrefix after}
    (supported : SupportedRotation rotation a b) :
    SupportedRotationExecution 1 a b :=
  .step rotation supported (.refl _)

end SupportedRotation

namespace SupportedRotationExecution

theorem leftContext {length lower root upper : ℕ} {before after : BST lower root}
    {a : RootPrefix before} {b : RootPrefix after}
    (execution : SupportedRotationExecution length a b)
    {right : BST (root + 1) upper} (rightPrefix : RootPrefix right) :
    SupportedRotationExecution length (.node a rightPrefix) (.node b rightPrefix) := by
  induction execution with
  | refl => exact .refl _
  | step rotation supported tail ih =>
      exact .step (.leftContext rotation _) (.leftContext rotation supported _ _) (ih _)

theorem rightContext {length lower root upper : ℕ}
    {before after : BST (root + 1) upper}
    {a : RootPrefix before} {b : RootPrefix after}
    {left : BST lower root} (leftPrefix : RootPrefix left)
    (execution : SupportedRotationExecution length a b) :
    SupportedRotationExecution length (.node leftPrefix a) (.node leftPrefix b) := by
  induction length generalizing before after with
  | zero => cases execution; exact .refl _
  | succ length ih =>
      cases execution with
      | step rotation supported tail =>
          exact .step (.rightContext _ rotation) (.rightContext _ _ rotation supported)
            (ih tail)

theorem append {firstLength secondLength lower upper : ℕ}
    {before middle after : BST lower upper}
    {a : RootPrefix before} {b : RootPrefix middle} {c : RootPrefix after}
    (first : SupportedRotationExecution firstLength a b)
    (second : SupportedRotationExecution secondLength b c) :
    SupportedRotationExecution (firstLength + secondLength) a c := by
  induction first with
  | refl => simpa using second
  | step rotation supported tail ih =>
      simpa [Nat.succ_add] using .step rotation supported (ih second)

end SupportedRotationExecution

namespace SupportedRotation

/-- A rotation in a hanging subtree commutes past one supported rotation. -/
theorem commute_outside
    {depth lower upper : ℕ} {before after : BST lower upper}
    {rotation : RotationAt depth before after}
    {a : RootPrefix before} {b : RootPrefix after}
    (supported : SupportedRotation rotation a b)
    {earlier : BST lower upper} {earlierPrefix : RootPrefix earlier}
    (outside : OutsideRotation earlierPrefix a) :
    ∃ (middle : BST lower upper) (middlePrefix : RootPrefix middle),
      SupportedRotationExecution 1 earlierPrefix middlePrefix ∧
        OutsideRotation middlePrefix b := by
  induction supported with
  | rootRight x y z px py pz =>
      cases outside with
      | left inner rightPrefix =>
          cases inner with
          | left first middlePrefix =>
              exact ⟨_, _, (SupportedRotation.rootRight _ _ _ _ _ _).toExecution,
                .left first _⟩
          | right leftPrefix second =>
              exact ⟨_, _, (SupportedRotation.rootRight _ _ _ _ _ _).toExecution,
                .right _ (.left second _)⟩
      | right leftPrefix third =>
          exact ⟨_, _, (SupportedRotation.rootRight _ _ _ _ _ _).toExecution,
            .right _ (.right _ third)⟩
  | rootLeft x y z px py pz =>
      cases outside with
      | left first rightPrefix =>
          exact ⟨_, _, (SupportedRotation.rootLeft _ _ _ _ _ _).toExecution,
            .left (.left first _) _⟩
      | right leftPrefix inner =>
          cases inner with
          | left second rightPrefix =>
              exact ⟨_, _, (SupportedRotation.rootLeft _ _ _ _ _ _).toExecution,
                .left (.right _ second) _⟩
          | right middlePrefix third =>
              exact ⟨_, _, (SupportedRotation.rootLeft _ _ _ _ _ _).toExecution,
                .right _ third⟩
  | leftContext rotation supported right rightPrefix ih =>
      cases outside with
      | left inner rightPrefix =>
          obtain ⟨middle, middlePrefix, first, rest⟩ := ih inner
          exact ⟨_, _, first.leftContext rightPrefix, .left rest _⟩
      | right leftPrefix other =>
          exact ⟨_, _, (SupportedRotation.leftContext rotation supported _ _).toExecution,
            .right _ other⟩
  | rightContext left leftPrefix rotation supported ih =>
      cases outside with
      | left other rightPrefix =>
          exact ⟨_, _, (SupportedRotation.rightContext _ _ rotation supported).toExecution,
            .left other _⟩
      | right leftPrefix inner =>
          obtain ⟨middle, middlePrefix, first, rest⟩ := ih inner
          exact ⟨_, _, first.rightContext leftPrefix, .right _ rest⟩

end SupportedRotation

namespace SupportedRotationExecution

/-- Move one hanging-subtree rotation to the end of a supported execution. -/
theorem commute_outside {length lower upper : ℕ} {before after : BST lower upper}
    {a : RootPrefix before} {b : RootPrefix after}
    (execution : SupportedRotationExecution length a b)
    {earlier : BST lower upper} {earlierPrefix : RootPrefix earlier}
    (outside : OutsideRotation earlierPrefix a) :
    ∃ (middle : BST lower upper) (middlePrefix : RootPrefix middle),
      SupportedRotationExecution length earlierPrefix middlePrefix ∧
        OutsideRotation middlePrefix b := by
  induction execution with
  | refl => exact ⟨_, _, .refl _, outside⟩
  | step rotation supported tail ih =>
      obtain ⟨firstMiddle, firstPrefix, first, deferred⟩ :=
        supported.commute_outside outside
      obtain ⟨last, lastPrefix, rest, lastDeferred⟩ := ih deferred
      exact ⟨last, lastPrefix, by simpa [Nat.add_comm] using first.append rest,
        lastDeferred⟩

end SupportedRotationExecution

namespace RotationAt

/-- Pull a selected prefix backwards through a rotation. Either the rotation
is outside it, or selecting at most one additional node supports the step. -/
theorem prepare_selected {depth lower upper : ℕ} {before after : BST lower upper}
    (rotation : RotationAt depth before after) (selected : RootPrefix after) :
    (∃ earlier : RootPrefix before, OutsideRotation earlier selected) ∨
      ∃ (earlier : RootPrefix before) (enlarged : RootPrefix after),
        selected.Refines enlarged ∧ SupportedRotation rotation earlier enlarged ∧
          earlier.card ≤ selected.card + 1 := by
  induction rotation with
  | root rootRotation =>
      cases rootRotation with
      | right x y z =>
          cases selected with
          | none => exact .inl ⟨_, .hidden (.root (.right x y z))⟩
          | node px rest =>
              cases rest with
              | none =>
                  refine .inr ⟨.node (.node px (.none y)) (.none z),
                    .node px (.node (.none y) (.none z)),
                    .node (.refl _) (.none _), .rootRight _ _ _ _ _ _, ?_⟩
                  simp only [RootPrefix.card]
                  omega
              | node py pz =>
                  refine .inr ⟨_, _, .refl _, .rootRight _ _ _ _ _ _, ?_⟩
                  simp only [RootPrefix.card]
                  omega
      | left x y z =>
          cases selected with
          | none => exact .inl ⟨_, .hidden (.root (.left x y z))⟩
          | node rest pz =>
              cases rest with
              | none =>
                  refine .inr ⟨.node (.none x) (.node (.none y) pz),
                    .node (.node (.none x) (.none y)) pz,
                    .node (.none _) (.refl _), .rootLeft _ _ _ _ _ _, ?_⟩
                  simp only [RootPrefix.card]
                  omega
              | node px py =>
                  refine .inr ⟨_, _, .refl _, .rootLeft _ _ _ _ _ _, ?_⟩
                  simp only [RootPrefix.card]
                  omega
  | leftContext rotation right ih =>
      cases selected with
      | none => exact .inl ⟨_, .hidden (.leftContext rotation right)⟩
      | node leftSelected rightSelected =>
          rcases ih leftSelected with ⟨earlier, outside⟩ | ⟨earlier, enlarged, larger, supported, bound⟩
          · exact .inl ⟨_, .left outside rightSelected⟩
          · refine .inr ⟨_, _, .node larger (.refl _),
              .leftContext rotation supported _ rightSelected, ?_⟩
            simp only [RootPrefix.card]
            omega
  | rightContext left rotation ih =>
      cases selected with
      | none => exact .inl ⟨_, .hidden (.rightContext left rotation)⟩
      | node leftSelected rightSelected =>
          rcases ih rightSelected with ⟨earlier, outside⟩ | ⟨earlier, enlarged, larger, supported, bound⟩
          · exact .inl ⟨_, .right leftSelected outside⟩
          · refine .inr ⟨_, _, .node (.refl _) larger,
              .rightContext _ leftSelected rotation supported, ?_⟩
            simp only [RootPrefix.card]
            omega

end RotationAt

namespace RotationExecution

/-- Serve the final root using a small connected part of an execution, leaving
all postponed work as an ordinary rotation suffix with the original endpoint. -/
theorem factor_root {length lower upper key : ℕ} {before after : BST lower upper}
    (execution : RotationExecution length before after) (root : after.HasRoot key) :
    ∃ (served : BST lower upper) (kept deferred : ℕ)
      (initialPrefix : RootPrefix before) (servedPrefix : RootPrefix served),
      SupportedRotationExecution kept initialPrefix servedPrefix ∧
      0 < initialPrefix.card ∧ served.HasRoot key ∧
      RotationExecution deferred served after ∧
      kept + deferred = length ∧ initialPrefix.card ≤ kept + 1 := by
  induction execution with
  | refl =>
      obtain ⟨left, right, rfl⟩ := root
      refine ⟨_, 0, 0, .node (.none left) (.none right),
        .node (.none left) (.none right), .refl _, ?_,
        ⟨left, right, rfl⟩, .refl, rfl, ?_⟩ <;> simp [RootPrefix.card]
  | step rotation tail ih =>
      obtain ⟨served, kept, deferred, selected, lastSelected,
        supportedTail, positive, servedRoot, remainder, lengths, size⟩ := ih root
      rcases RotationAt.prepare_selected rotation selected with
        ⟨earlier, outside⟩ | ⟨earlier, enlarged, larger, supported, enlargedSize⟩
      · obtain ⟨earlierServed, earlierLast, keptExecution, late⟩ :=
          supportedTail.commute_outside outside
        have sameSize := outside.card_eq
        have lastSize := supportedTail.card_eq
        obtain ⟨lateDepth, lateRotation⟩ := late.exists_rotation
        refine ⟨earlierServed, kept, deferred + 1, earlier, earlierLast,
          keptExecution, by omega, late.root_before (by omega) servedRoot,
          ?_, by omega, by omega⟩
        exact .step lateRotation remainder
      · obtain ⟨enlargedLast, lastLarger, enlargedExecution⟩ :=
          supportedTail.refine larger
        have largerSize := larger.card_le
        have sameSize := supported.card_eq
        exact ⟨served, kept + 1, deferred, earlier, enlargedLast,
          .step rotation supported enlargedExecution,
          by omega, servedRoot, remainder, by omega, by omega⟩

end RotationExecution

/-- Postpone work outside the support of each root service. The initial tree
and request order are preserved, rotations are never duplicated, and the sum
of support sizes is at most the new rotation count plus the request count.
The final tree is unconstrained because unused postponed work is discarded. -/
theorem exists_connectedReordered
    {n rotations : ℕ} {accesses : List (Fin n)}
    {before after : BST 0 n}
    (execution : OfflineOptimum.Execution accesses before after rotations) :
    ∃ (targetAfter : BST 0 n) (targetRotations supportCharge : ℕ),
      ConnectedExecution accesses before targetAfter targetRotations supportCharge ∧
      targetRotations ≤ rotations ∧
      supportCharge ≤ accesses.length + targetRotations := by
  induction accesses generalizing before after rotations with
  | nil => exact ⟨before, 0, 0, .done before, by omega, by simp⟩
  | cons access accesses ih =>
      cases execution with
      | @next _ _ _ served after headRotations tailRotations head root tail =>
          obtain ⟨middle, kept, deferred, initialPrefix, middlePrefix,
            supported, positive, middleRoot, remainder, lengths, size⟩ :=
            RotationExecution.factor_root head root
          by_cases empty : accesses = []
          · subst accesses
            refine ⟨middle, kept, initialPrefix.card, ?_, by omega, ?_⟩
            · simpa using ConnectedExecution.next supported positive middleRoot (.done middle)
            · simp only [List.length_cons, List.length_nil]
              omega
          · obtain ⟨target, targetRotations, targetCharge, targetExecution,
              targetBound, chargeBound⟩ :=
              ih (OfflineOptimum.Execution.prependRotations empty remainder tail)
            refine ⟨target, kept + targetRotations, initialPrefix.card + targetCharge,
              .next supported positive middleRoot targetExecution, by omega, ?_⟩
            simp only [List.length_cons]
            omega

/-- Uniform constant-factor comparison with the original arbitrary-rotation
optimum. No structural normal-form or model-equivalence axiom is used. -/
theorem connectedOptCost_le_two_mul_offlineOptCost
    {n : ℕ} (accesses : List (Fin n)) :
    connectedOptCost accesses ≤ 2 * OfflineOptimum.offlineOptCost accesses := by
  obtain ⟨before, after, rotations, execution, costEq⟩ :=
    OfflineOptimum.exists_optimalExecution_eq accesses
  obtain ⟨target, targetRotations, supportCharge, connected, rotationBound, chargeBound⟩ :=
    exists_connectedReordered execution
  calc
    connectedOptCost accesses ≤ accesses.length + targetRotations + supportCharge :=
      connectedOptCost_le ⟨before, target, targetRotations, supportCharge, connected, rfl⟩
    _ ≤ 2 * OfflineOptimum.offlineOptCost accesses := by omega

/-- The former model-equivalence assumption, with explicit multiplier two. -/
theorem uniformConnectedSupportNormalization : UniformConnectedSupportNormalization :=
  ⟨2, fun _ accesses => connectedOptCost_le_two_mul_offlineOptCost accesses⟩

end Splay.Accounting.OfflineConnectedSupport

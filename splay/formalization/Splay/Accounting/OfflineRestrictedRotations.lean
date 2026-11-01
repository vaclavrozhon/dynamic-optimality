import Splay.Accounting.OfflineSupportFrontier
import Splay.Accounting.OfflineSupportedPath

namespace Splay.Accounting.OfflineConnectedSupport

open Splay.Tree.BST
open OfflineNormalForm RestrictedSpines

/-- A forward path in the canonical conversion. All rotations have depth at
most one, and one spine invariant is preserved for the entire path. -/
structure CanonicalPath {lower upper : ℕ} {before after : BST lower upper}
    (a : RootPrefix before) (b : RootPrefix after) where
  path : SupportedPath a b
  depthBound : path.DepthBound 1
  preservesSpines : ∀ slack, SpineSafe before slack →
    path.ForallTrees (fun tree => SpineSafe tree slack)

namespace CanonicalPath

def nil {lower upper : ℕ} {tree : BST lower upper} (selected : RootPrefix tree) :
    CanonicalPath selected selected := ⟨.nil _, trivial, fun _ safe => safe⟩

def append {lower upper : ℕ} {before middle after : BST lower upper}
    {a : RootPrefix before} {b : RootPrefix middle} {c : RootPrefix after}
    (first : CanonicalPath a b) (second : CanonicalPath b c) : CanonicalPath a c where
  path := first.path.append second.path
  depthBound := (SupportedPath.depthBound_append _ _ _).mpr ⟨first.depthBound, second.depthBound⟩
  preservesSpines := fun slack safe => (SupportedPath.forallTrees_append _ _ _).mpr
    ⟨first.preservesSpines slack safe,
      second.preservesSpines slack (first.preservesSpines slack safe).final⟩

def rootLeft {lower first second upper : ℕ}
    {a : BST lower first} {b : BST (first + 1) second} {c : BST (second + 1) upper}
    (pa : RootPrefix a) (pb : RootPrefix b) (pc : RootPrefix c) :
    CanonicalPath (.node pa (.node pb pc)) (.node (.node pa pb) pc) where
  path := .cons (.root (.left a b c)) (.rootLeft _ _ _ _ _ _) (.nil _)
  depthBound := ⟨by decide, trivial⟩
  preservesSpines := fun _ safe => ⟨safe, safe.rootRotate (.left _ _ _)⟩

def rootRight {lower first second upper : ℕ}
    {a : BST lower first} {b : BST (first + 1) second} {c : BST (second + 1) upper}
    (pa : RootPrefix a) (pb : RootPrefix b) (pc : RootPrefix c) :
    CanonicalPath (.node (.node pa pb) pc) (.node pa (.node pb pc)) where
  path := .cons (.root (.right a b c)) (.rootRight _ _ _ _ _ _) (.nil _)
  depthBound := ⟨by decide, trivial⟩
  preservesSpines := fun _ safe => ⟨safe, safe.rootRotate (.right _ _ _)⟩

def leftChildLeft {lower first second root upper : ℕ}
    {a : BST lower first} {b : BST (first + 1) second}
    {c : BST (second + 1) root} {d : BST (root + 1) upper}
    (pa : RootPrefix a) (pb : RootPrefix b) (pc : RootPrefix c) (pd : RootPrefix d) :
    CanonicalPath (.node (.node pa (.node pb pc)) pd)
      (.node (.node (.node pa pb) pc) pd) where
  path := .cons (.leftContext (.root (.left _ _ _)) _)
    (.leftContext _ (.rootLeft _ _ _ _ _ _) _ _) (.nil _)
  depthBound := ⟨by decide, trivial⟩
  preservesSpines := fun _ safe => ⟨safe, safe.leftChildLeft⟩

end CanonicalPath

/-- First raise the maximum selected key using only left root rotations.
Each such rotation adds exactly one selected node to the left spine. -/
theorem exists_maxRoot {lower upper : ℕ} {tree : BST lower upper}
    (selected : RootPrefix tree) (positive : 0 < selected.card) :
    ∃ (root : ℕ) (left : BST lower root) (right : BST (root + 1) upper)
      (leftSelected : RootPrefix left)
      (path : CanonicalPath selected (.node leftSelected (.none right))),
      path.path.length + selected.leftSpine = leftSelected.leftSpine + 1 ∧
      path.path.length + 1 = selected.rightSpine := by
  generalize measure_eq : selected.rightSpine = measure
  induction measure using Nat.strong_induction_on generalizing tree with
  | h measure ih =>
      cases selected with
      | none => simp [RootPrefix.card] at positive
      | node left right =>
          cases right with
          | none => exact ⟨_, _, _, left, .nil _, by simp [CanonicalPath.nil, SupportedPath.length,
              RootPrefix.leftSpine], by
                simpa [CanonicalPath.nil, SupportedPath.length, RootPrefix.rightSpine]
                  using measure_eq⟩
          | node middle right =>
              obtain ⟨root, finalLeft, finalRight, finalSelected, tail, leftCount, rightCount⟩ :=
                ih _ (by simp only [RootPrefix.rightSpine] at measure_eq ⊢; omega)
                  (.node (.node left middle) right)
                  (by simp only [RootPrefix.card]; omega) rfl
              refine ⟨root, finalLeft, finalRight, finalSelected,
                (CanonicalPath.rootLeft left middle right).append tail, ?_, ?_⟩
              · simp only [CanonicalPath.append, SupportedPath.length_append,
                  CanonicalPath.rootLeft, SupportedPath.length, RootPrefix.leftSpine] at *
                omega
              · simp only [CanonicalPath.append, SupportedPath.length_append,
                  CanonicalPath.rootLeft, SupportedPath.length, RootPrefix.rightSpine] at *
                omega

/-- Scan down through the remaining selected left subtree. A left-child
rotation increases its left-spine length; a right root rotation removes one
selected node. Both decrease `2 * card - leftSpine` by exactly one. -/
theorem exists_scanToVine {lower root upper : ℕ}
    {left : BST lower root} {right : BST (root + 1) upper}
    (leftSelected : RootPrefix left) (rightSelected : RootPrefix right)
    (rightVine : rightSelected.IsRightVine) :
    ∃ (target : BST lower upper) (targetSelected : RootPrefix target)
      (path : CanonicalPath (.node leftSelected rightSelected) targetSelected),
      targetSelected.IsRightVine ∧
      path.path.length = 2 * leftSelected.card - leftSelected.leftSpine ∧
      (∀ key, key ∈ leftSelected.keys ∨ key = root → path.path.Visits key) := by
  generalize measure_eq : 2 * leftSelected.card - leftSelected.leftSpine = measure
  induction measure using Nat.strong_induction_on generalizing root with
  | h measure ih =>
      cases leftSelected with
      | none =>
          refine ⟨_, _, .nil _, rightVine, ?_, ?_⟩
          · simpa [CanonicalPath.nil, SupportedPath.length, RootPrefix.card, RootPrefix.leftSpine]
              using measure_eq
          · intro key member
            have equal : key = root := by simpa [RootPrefix.keys] using member
            subst key
            exact ⟨_, _, rfl⟩
      | @node lower first root a b pa pb =>
          cases pb with
          | none =>
              obtain ⟨target, selected, tail, vine, count, visits⟩ :=
                ih _ (by
                  have small := pa.leftSpine_le_card
                  simp only [RootPrefix.card, RootPrefix.leftSpine] at measure_eq ⊢
                  omega) pa (.node (.none b) rightSelected) rightVine rfl
              refine ⟨target, selected, (CanonicalPath.rootRight pa (.none b) rightSelected).append tail,
                vine, ?_, ?_⟩
              · have small := pa.leftSpine_le_card
                simp only [CanonicalPath.append, SupportedPath.length_append,
                  CanonicalPath.rootRight, SupportedPath.length, RootPrefix.card,
                  RootPrefix.leftSpine] at *
                omega
              · intro key member
                change (Splay.Tree.BST.node (.node a b) right).HasRoot key ∨ tail.path.Visits key
                by_cases equal : key = root
                · subst key
                  exact .inl ⟨_, _, rfl⟩
                · exact .inr (visits key (by simpa [RootPrefix.keys, equal] using member))
          | @node _ second _ b c pb pc =>
              obtain ⟨target, selected, tail, vine, count, visits⟩ :=
                ih _ (by
                  have small := pa.leftSpine_le_card
                  simp only [RootPrefix.card, RootPrefix.leftSpine] at measure_eq ⊢
                  omega) (.node (.node pa pb) pc) rightSelected rightVine rfl
              refine ⟨target, selected, (CanonicalPath.leftChildLeft pa pb pc rightSelected).append tail,
                vine, ?_, ?_⟩
              · have small := pa.leftSpine_le_card
                simp only [CanonicalPath.append, SupportedPath.length_append,
                  CanonicalPath.leftChildLeft, SupportedPath.length, RootPrefix.card,
                  RootPrefix.leftSpine] at *
                omega
              · intro key member
                change (Splay.Tree.BST.node (.node a (.node b c)) right).HasRoot key ∨ tail.path.Visits key
                apply Or.inr
                apply visits key
                simpa only [RootPrefix.keys, List.mem_append, List.mem_cons, or_assoc] using member

/-- Convert any nonempty root support to its unique inorder right vine. The
path visits every selected key at the root and uses at most `2 * card - 2`
rotations, all at depth zero or one. -/
theorem exists_canonicalPath {lower upper : ℕ} {tree : BST lower upper}
    (selected : RootPrefix tree) (positive : 0 < selected.card) :
    ∃ path : CanonicalPath selected selected.frontier.selected,
      path.path.length + 2 ≤ 2 * selected.card ∧
        ∀ key, key ∈ selected.keys → path.path.Visits key := by
  obtain ⟨root, left, right, leftSelected, first, leftCount, rightCount⟩ :=
    exists_maxRoot selected positive
  obtain ⟨target, targetSelected, second, vine, count, visits⟩ :=
    exists_scanToVine leftSelected (.none right) trivial
  let path := first.append second
  have sameFrontier := path.path.toExecution.frontier_eq
  have packed := targetSelected.pack_eq_frontier_of_isRightVine vine
  rw [← sameFrontier] at packed
  have packedExists :
      ∃ path : CanonicalPath selected targetSelected,
        path.path.length + 2 ≤ 2 * selected.card ∧
          ∀ key, key ∈ selected.keys → path.path.Visits key := by
    refine ⟨path, ?_, ?_⟩
    · have sameCard := first.path.toExecution.card_eq
      have small := leftSelected.leftSpine_le_card
      have initialPositive : 0 < selected.leftSpine := by
        cases selected with
        | none => simp [RootPrefix.card] at positive
        | node => simp [RootPrefix.leftSpine]
      simp only [path, CanonicalPath.append, SupportedPath.length_append, RootPrefix.card] at *
      omega
    · intro key member
      apply (SupportedPath.visits_append _ _).mpr
      apply Or.inr
      apply visits key
      have keys := first.path.toExecution.keys_eq
      rw [keys] at member
      simpa [RootPrefix.keys] using member
  cases packed
  exact packedExists

/-- The corrected restricted-rotation lemma on an explicit common support.
All untouched hanging subtrees are preserved. Every selected key is visited
at the root, even when the two endpoint trees happen to be identical. -/
theorem exists_restrictedPath_of_sameFrontier
    {lower upper slack : ℕ} {before after : BST lower upper}
    (a : RootPrefix before) (b : RootPrefix after)
    (same : a.frontier = b.frontier) (positive : 0 < a.card)
    (beforeRibs : HasBoundedMinorRibs before slack)
    (afterRibs : HasBoundedMinorRibs after slack) :
    ∃ path : SupportedPath a b,
      path.length + 4 ≤ 4 * a.card ∧ path.DepthBound 1 ∧
      path.ForallTrees (fun tree => tree.height ≤ max before.height after.height + a.card) ∧
      path.ForallTrees (fun tree => HasBoundedMinorRibs tree (slack + 1)) ∧
      ∀ key, key ∈ a.keys → path.Visits key := by
  have sameCard : a.card = b.card := by
    simpa using congrArg SupportFrontier.card same
  obtain ⟨first, firstCost, firstVisits⟩ := exists_canonicalPath a positive
  have secondExists : ∃ second : CanonicalPath b a.frontier.selected,
      second.path.length + 2 ≤ 2 * b.card ∧
        ∀ key, key ∈ b.keys → second.path.Visits key := by
    rw [same]
    exact exists_canonicalPath b (by omega)
  obtain ⟨second, secondCost, secondVisits⟩ := secondExists
  refine ⟨first.path.append second.path.reverse, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [SupportedPath.length_append, SupportedPath.length_reverse]
    omega
  · exact (SupportedPath.depthBound_append _ _ _).mpr
      ⟨first.depthBound, second.depthBound.reverse⟩
  · apply (SupportedPath.forallTrees_append _ _ _).mpr
    constructor
    · exact first.path.forall_height_le.imp (fun tree bound => by omega)
    · apply SupportedPath.ForallTrees.reverse
      exact second.path.forall_height_le.imp (fun tree bound => by omega)
  · apply (SupportedPath.forallTrees_append _ _ _).mpr
    constructor
    · exact (first.preservesSpines slack (spineSafe_of_ribs beforeRibs)).imp
        (fun _ safe => safe.ribs)
    · exact ((second.preservesSpines slack (spineSafe_of_ribs afterRibs)).imp
        (fun _ safe => safe.ribs)).reverse
  · intro key member
    exact (SupportedPath.visits_append _ _).mpr (.inl (firstVisits key member))

end Splay.Accounting.OfflineConnectedSupport

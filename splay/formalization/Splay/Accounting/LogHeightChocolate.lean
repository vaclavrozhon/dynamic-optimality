import Splay.Accounting.OfflineSkeletonSubstitution
import Splay.Accounting.OfflineHeavyPaths

/-!
# Weighted stacks on literal BST subtrees

This is the weighted stack used in the logarithmic-height simulation. A
payload is a literal untouched BST subtree, with positive weight `size + 1`.
Perfect binary crumbs group payloads. Each active layer has one, two, or
three regular crumbs; an icing stack stores frozen heavier fragments.
The constructor inequalities are the thick-icing invariant of the Chocolate
Pop-Tart of Bose, Collette, Fagerberg, and Langerman (2012, Lemma 4).
-/

namespace Splay.Accounting.OfflineConnectedSupport.LogHeightChocolate

open Splay.Tree OfflineNormalForm

/-- The positive leaf weight contributed by a literal subtree. -/
def mass {lower upper : ℕ} (tree : BST lower upper) : ℕ := tree.size + 1

def logMass {lower upper : ℕ} (tree : BST lower upper) : ℕ := Nat.log 2 (mass tree)

/-- A perfect skeleton with `2^level` untouched payloads. -/
inductive Crumb : ℕ → {lower upper : ℕ} → BST lower upper → Type
  | leaf {lower upper : ℕ} (payload : BST lower upper) : Crumb 0 payload
  | join {level lower root upper : ℕ} {left : BST lower root} {right : BST (root + 1) upper}
      (a : Crumb level left) (b : Crumb level right) : Crumb (level + 1) (.node left right)

/-- `false` denotes an active layer and `true` its icing. Frozen fragments
retain the old active layer, so pop can restore it by literal rotations. -/
inductive Chocolate : Bool → ℕ → {lower upper : ℕ} → BST lower upper → Type
  | base {level lower upper : ℕ} {tree : BST lower upper}
      (crumb : Crumb level tree) : Chocolate false level tree
  | oneEnd {level lower k0 upper : ℕ}
      {a : BST lower k0}
      {icing : BST (k0 + 1) upper}
      (crumb0 : Crumb level a)
      (frozen : Chocolate true level icing)
      : Chocolate false level (.node a icing)
  | twoEnd {level lower k0 k1 upper : ℕ}
      {a : BST lower k0}
      {b : BST (k0 + 1) k1}
      {icing : BST (k1 + 1) upper}
      (crumb0 : Crumb level a)
      (crumb1 : Crumb level b)
      (frozen : Chocolate true level icing)
      : Chocolate false level (.node a (.node b icing))
  | threeEnd {level lower k0 k1 k2 upper : ℕ}
      {a : BST lower k0}
      {b : BST (k0 + 1) k1}
      {c : BST (k1 + 1) k2}
      {icing : BST (k2 + 1) upper}
      (crumb0 : Crumb level a)
      (crumb1 : Crumb level b)
      (crumb2 : Crumb level c)
      (frozen : Chocolate true level icing)
      : Chocolate false level (.node a (.node b (.node c icing)))
  | oneNext {level lower k0 pivot upper : ℕ}
      {a : BST lower k0}
      {next : BST (k0 + 1) pivot} {icing : BST (pivot + 1) upper}
      (crumb0 : Crumb level a)
      (layer : Chocolate false (level + 1) next)
      (frozen : Chocolate true level icing)
      (thin : mass next < mass icing)
      : Chocolate false level (.node a (.node next icing))
  | twoNext {level lower k0 k1 pivot upper : ℕ}
      {a : BST lower k0}
      {b : BST (k0 + 1) k1}
      {next : BST (k1 + 1) pivot} {icing : BST (pivot + 1) upper}
      (crumb0 : Crumb level a)
      (crumb1 : Crumb level b)
      (layer : Chocolate false (level + 1) next)
      (frozen : Chocolate true level icing)
      (thin : mass next < mass icing)
      : Chocolate false level (.node a (.node b (.node next icing)))
  | threeNext {level lower k0 k1 k2 pivot upper : ℕ}
      {a : BST lower k0}
      {b : BST (k0 + 1) k1}
      {c : BST (k1 + 1) k2}
      {next : BST (k2 + 1) pivot} {icing : BST (pivot + 1) upper}
      (crumb0 : Crumb level a)
      (crumb1 : Crumb level b)
      (crumb2 : Crumb level c)
      (layer : Chocolate false (level + 1) next)
      (frozen : Chocolate true level icing)
      (thin : mass next < mass icing)
      : Chocolate false level (.node a (.node b (.node c (.node next icing))))
  | icingBase {level lower upper : ℕ} {tree : BST lower upper}
      (crumb : Crumb level tree) : Chocolate true level tree
  | freezeCrumb {level lower root upper : ℕ}
      {crumbTree : BST lower root} {icing : BST (root + 1) upper}
      (crumb : Crumb (level + 1) crumbTree) (frozen : Chocolate true level icing)
      (thick : mass icing ≤ mass crumbTree) : Chocolate true level (.node crumbTree icing)
  | freezeLayer {level lower first second upper : ℕ}
      {crumbTree : BST lower first} {next : BST (first + 1) second} {icing : BST (second + 1) upper}
      (crumb : Crumb (level + 1) crumbTree) (layer : Chocolate false (level + 1) next)
      (frozen : Chocolate true level icing) (thin : mass next < mass icing)
      (thick : mass icing ≤ mass (.node crumbTree next)) :
      Chocolate true level (.node (.node crumbTree next) icing)

abbrev Layer := Chocolate false
abbrev Icing := Chocolate true

namespace Crumb

def selected : {level lower upper : ℕ} → {tree : BST lower upper} → Crumb level tree → RootPrefix tree
  | _, _, _, _, .leaf payload => .none payload
  | _, _, _, _, .join a b => .node a.selected b.selected

theorem selected_card {level lower upper : ℕ} {tree : BST lower upper} (crumb : Crumb level tree) :
    crumb.selected.card + 1 = 2 ^ level := by
  induction crumb with
  | leaf => simp [selected, RootPrefix.card]
  | join a b ihA ihB => simp only [selected, RootPrefix.card, pow_succ]; omega

end Crumb

namespace Chocolate

def selected : {kind : Bool} → {level lower upper : ℕ} → {tree : BST lower upper} →
    Chocolate kind level tree → RootPrefix tree
  | _, _, _, _, _, .base crumb => crumb.selected

  | _, _, _, _, _, .oneEnd a icing => (.node a.selected icing.selected)
  | _, _, _, _, _, .twoEnd a b icing => (.node a.selected (.node b.selected icing.selected))
  | _, _, _, _, _, .threeEnd a b c icing => (.node a.selected (.node b.selected (.node c.selected icing.selected)))
  | _, _, _, _, _, .oneNext a layer icing _ => (.node a.selected (.node layer.selected icing.selected))
  | _, _, _, _, _, .twoNext a b layer icing _ => (.node a.selected (.node b.selected (.node layer.selected icing.selected)))
  | _, _, _, _, _, .threeNext a b c layer icing _ => (.node a.selected (.node b.selected (.node c.selected (.node layer.selected icing.selected))))
  | _, _, _, _, _, .icingBase crumb => crumb.selected
  | _, _, _, _, _, .freezeCrumb crumb icing _ => .node crumb.selected icing.selected
  | _, _, _, _, _, .freezeLayer crumb layer icing _ _ => .node (.node crumb.selected layer.selected) icing.selected

/-- One unit pays for an active non-full layer; frozen layers retain their
credit until defrosted. The multiplier needed for rotations is supplied at
simulation time. -/
def potential : {kind : Bool} → {level lower upper : ℕ} → {tree : BST lower upper} →
    Chocolate kind level tree → ℕ
  | _, _, _, _, _, .base _ => 0
  | _, _, _, _, _, .oneEnd _ icing => 1 + icing.potential
  | _, _, _, _, _, .twoEnd _ _ icing => icing.potential
  | _, _, _, _, _, .threeEnd _ _ _ icing => 1 + icing.potential
  | _, _, _, _, _, .oneNext _ layer icing _ => 1 + layer.potential + icing.potential
  | _, _, _, _, _, .twoNext _ _ layer icing _ => layer.potential + icing.potential
  | _, _, _, _, _, .threeNext _ _ _ layer icing _ => 1 + layer.potential + icing.potential
  | _, _, _, _, _, .icingBase _ => 0
  | _, _, _, _, _, .freezeCrumb _ icing _ => icing.potential
  | _, _, _, _, _, .freezeLayer _ layer icing _ _ => layer.potential + icing.potential

theorem potential_le_card {kind : Bool} {level lower upper : ℕ} {tree : BST lower upper}
    (shaped : Chocolate kind level tree) : shaped.potential ≤ shaped.selected.card := by
  induction shaped <;> simp only [potential, selected, RootPrefix.card] at * <;> omega

end Chocolate

/-- At a payload, charge seven times the lower binary logarithm of its
positive weight; at each actual skeleton node, charge its traversed edge. -/
def weightedHeight {lower upper : ℕ} {tree : BST lower upper} : RootPrefix tree → ℕ
  | .none payload => 7 * logMass payload
  | .node left right => max (weightedHeight left) (weightedHeight right) + 1

theorem logMass_mono {lower upper lo hi : ℕ} {before : BST lower upper} {after : BST lo hi}
    (bound : mass before ≤ mass after) : logMass before ≤ logMass after := Nat.log_mono_right bound

theorem logMass_half {lower upper lo hi : ℕ} {before : BST lower upper} {after : BST lo hi}
    (bound : 2 * mass before ≤ mass after) : logMass before + 1 ≤ logMass after := by
  have monotone : Nat.log 2 (mass before * 2) ≤ Nat.log 2 (mass after) :=
    Nat.log_mono_right (by omega)
  rw [Nat.log_mul_base (by decide) (by simp [mass])] at monotone
  exact monotone

theorem Crumb.weightedHeight_le {level lower upper : ℕ} {tree : BST lower upper}
    (crumb : Crumb level tree) : weightedHeight crumb.selected ≤ 7 * logMass tree + level := by
  induction crumb with
  | leaf => simp [Crumb.selected, weightedHeight]
  | @join level lower root upper leftTree rightTree a b ihA ihB =>
      have left := logMass_mono (before := leftTree) (after := BST.node leftTree rightTree)
        (by simp only [mass, BST.size]; omega)
      have right := logMass_mono (before := rightTree) (after := BST.node leftTree rightTree)
        (by simp only [mass, BST.size]; omega)
      simp only [Crumb.selected, weightedHeight]
      omega

end Splay.Accounting.OfflineConnectedSupport.LogHeightChocolate

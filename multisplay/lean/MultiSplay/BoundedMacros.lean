import MultiSplay.SupportedPointer
import Splay.Accounting.OfflineRestrictedMacros

/-!
# Intermediate geometry of sparse normalizer macros

Unlike the existing full-universe trace type, `Path` accepts any ordinal
interval. Every rotation has depth at most one, every intermediate tree has the
specified height and minor-rib bounds, and the exact endpoints are retained.
-/

namespace MultiSplay.BoundedMacros

open Splay.Tree (BST)
open Splay.Accounting.OfflineNormalForm (HasBoundedMinorRibs)
open Splay.Accounting.OfflineConnectedSupport
  (HasSupportedPath RootPrefix SupportedPath exists_restrictedPath_of_sameFrontier)
open ChaCha.Paper20261030.Auxiliary (Rearranges rearranges_refl)

inductive Path (height slack : Nat) : {lower upper : Nat} → BST lower upper → BST lower upper → Nat → Prop
  | nil {lower upper : Nat} (source : BST lower upper)
      (bounded : source.height ≤ height) (ribs : HasBoundedMinorRibs source slack) :
      Path height slack source source 0
  | cons {lower upper depth count : Nat} {source middle target : BST lower upper}
      (rotation : BST.RotationAt depth source middle) (shallow : depth ≤ 1)
      (bounded : source.height ≤ height) (ribs : HasBoundedMinorRibs source slack)
      (tail : Path height slack middle target count) : Path height slack source target (count + 1)

theorem Path.append {height slack lower upper first second : Nat} {a b c : BST lower upper}
    (before : Path height slack a b first) (after : Path height slack b c second) :
    Path height slack a c (first + second) := by
  induction before with
  | nil => simpa using after
  | cons rotation shallow bounded ribs tail ih =>
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        Path.cons rotation shallow bounded ribs (ih after)

theorem ribs_mono {lower upper a b : Nat} (source : BST lower upper)
    (ribs : HasBoundedMinorRibs source a) (le : a ≤ b) : HasBoundedMinorRibs source b := by
  induction source with
  | empty => trivial
  | node left right ihl ihr => exact ⟨ribs.1.trans le, ribs.2.1.trans le, ihl ribs.2.2.1, ihr ribs.2.2.2⟩

theorem Path.mono {height slack height' slack' lower upper count : Nat} {a b : BST lower upper}
    (path : Path height slack a b count) (heightLe : height ≤ height') (slackLe : slack ≤ slack') :
    Path height' slack' a b count := by
  induction path with
  | nil source bounded ribs => exact .nil source (bounded.trans heightLe) (ribs_mono source ribs slackLe)
  | cons rotation shallow bounded ribs tail ih =>
      exact .cons rotation shallow (bounded.trans heightLe) (ribs_mono _ ribs slackLe) ih

theorem Path.rearranges {height slack lower upper count : Nat} {a b : BST lower upper}
    (path : Path height slack a b count) :
    Rearranges (DynamicOptimality.BST.toRaw a) (DynamicOptimality.BST.toRaw b) (3 * count) := by
  induction path with
  | nil => exact rearranges_refl _ 0
  | cons rotation shallow bounded ribs tail ih =>
      have first := DynamicOptimality.BST.rotation_pointer rotation
      have joined := first.trans ih
      exact joined.mono (by omega)

theorem of_supported_path {height slack lower upper : Nat} {a b : BST lower upper}
    {first : RootPrefix a} {last : RootPrefix b} (path : SupportedPath first last)
    (shallow : path.DepthBound 1) (heights : path.ForallTrees (fun tree => tree.height ≤ height))
    (ribs : path.ForallTrees (fun tree => HasBoundedMinorRibs tree slack)) :
    Path height slack a b path.length := by
  induction path with
  | nil => exact .nil _ heights ribs
  | cons rotation support tail ih => exact .cons rotation shallow.1 heights.1 ribs.1 (ih shallow.2 heights.2 ribs.2)

/-- The existing restricted-support theorem supplies the intermediate bounds;
endpoint bounds alone are not assumed to imply them. -/
theorem exists_path {height slack lower upper support rotations : Nat} {a b : BST lower upper}
    (execution : HasSupportedPath a b support rotations)
    (bounded : max a.height b.height + support ≤ height)
    (beforeRibs : HasBoundedMinorRibs a slack) (afterRibs : HasBoundedMinorRibs b slack) :
    ∃ count, Path height (slack + 1) a b count ∧ count ≤ 4 * support := by
  obtain ⟨first, last, path, card, _⟩ := execution
  by_cases positive : 0 < first.card
  · obtain ⟨restricted, lengthBound, shallow, heights, ribs, _⟩ :=
      exists_restrictedPath_of_sameFrontier first last path.toExecution.frontier_eq positive beforeRibs afterRibs
    exact ⟨restricted.length, of_supported_path restricted shallow
      (heights.imp (fun _ h => by omega)) ribs, by omega⟩
  · have same := path.eq_of_card_zero (by omega)
    subst b
    exact ⟨0, .nil a (by omega) (ribs_mono _ beforeRibs (by omega)), by omega⟩

end MultiSplay.BoundedMacros

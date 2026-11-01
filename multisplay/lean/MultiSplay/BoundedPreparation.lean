import MultiSplay.BoundedMacros
import MultiSplay.Alphabet

/-!
# Shape-certified preparation of sparse physical trees

Each segment records an actual shallow rotation path and its ordinal
interpretation. Bounds hold throughout the segment, not just at its endpoints.
Composition permits different ordinal origins without changing the physical
boundary tree. The charge is an upper bound on actual pointer work.
-/

namespace MultiSplay.BoundedMacros

open Splay.Tree (BST)
open DynamicOptimality (RawTree)
open Splay.Accounting.OfflineNormalForm (HasBoundedMinorRibs)
open TangoSquared.Paper20261030.Auxiliary (Rearranges)

variable {α : Type*}

def Geometry (height slack : Nat) (tree : RawTree α) : Prop :=
  ∃ (lower upper : Nat) (indexed : BST lower upper) (alphabet : Nat → α),
    Auxiliary.map alphabet (DynamicOptimality.BST.toRaw indexed) = tree ∧
    indexed.height ≤ height ∧ HasBoundedMinorRibs indexed slack

inductive Preparation (height slack : Nat) : RawTree α → RawTree α → Nat → Prop
  | segment {lower upper count cost : Nat} {before after : BST lower upper}
      (alphabet : Nat → α) (path : Path height slack before after count) (budget : 3 * count ≤ cost) :
      Preparation height slack (Auxiliary.map alphabet (DynamicOptimality.BST.toRaw before))
        (Auxiliary.map alphabet (DynamicOptimality.BST.toRaw after)) cost
  | trans {a b c : RawTree α} {first second : Nat}
      (left : Preparation height slack a b first) (right : Preparation height slack b c second) :
      Preparation height slack a c (first + second)

theorem Path.initial {height slack lower upper count : Nat} {a b : BST lower upper}
    (path : Path height slack a b count) : a.height ≤ height ∧ HasBoundedMinorRibs a slack := by
  cases path <;> simp_all

theorem Path.final {height slack lower upper count : Nat} {a b : BST lower upper}
    (path : Path height slack a b count) : b.height ≤ height ∧ HasBoundedMinorRibs b slack := by
  induction path with
  | nil _ h r => exact ⟨h, r⟩
  | cons _ _ _ _ _ ih => exact ih

theorem Preparation.geometry {height slack cost : Nat} {a b : RawTree α}
    (run : Preparation height slack a b cost) : Geometry height slack a ∧ Geometry height slack b := by
  induction run with
  | segment alphabet path budget => exact ⟨⟨_, _, _, alphabet, rfl, path.initial⟩, ⟨_, _, _, alphabet, rfl, path.final⟩⟩
  | trans left right ihl ihr => exact ⟨ihl.1, ihr.2⟩

theorem Preparation.rearranges {height slack cost : Nat} {a b : RawTree α}
    (run : Preparation height slack a b cost) : Rearranges a b cost := by
  induction run with
  | segment alphabet path budget => exact (Alphabet.rearranges alphabet path.rearranges).mono budget
  | trans left right ihl ihr => exact ihl.trans ihr

end MultiSplay.BoundedMacros

import DynamicOptimality.GeometricOnlineSimulation.DyadicCut
import DynamicOptimality.ModelOnline

/-!
# Perfect blocks with their actual hanging subtrees

A level `h` block has `2^h` external gaps and `2^h - 1` keys. A fragment
is an arbitrary binary skeleton with such blocks in its holes. Splitting a
block exposes only the path to the selected key. Its untouched siblings are
retained literally, and the resulting root transition has a linear bound
in the number of exposed nodes.
-/

namespace DynamicOptimality.GeometricOnlineSimulation

open ChaCha.MTR ChaCha.MTR.Pointer

variable {α : Type*}

/-- A complete binary shape, with no restriction on the labels. -/
inductive Perfect : Nat → RawTree α → Prop
  | empty : Perfect 0 .empty
  | node {level : Nat} {left right : RawTree α} (key : α)
      (first : Perfect level left) (last : Perfect level right) :
      Perfect (level + 1) (.node left key right)

theorem Perfect.gaps {level : Nat} {tree : RawTree α} (perfect : Perfect level tree) :
    tree.size + 1 = 2 ^ level := by
  induction perfect with
  | empty => rfl
  | node key first last ihl ihr => simp only [Tree.size, pow_succ]; omega

theorem Perfect.keys {level : Nat} {tree : RawTree α} (perfect : Perfect level tree) :
    tree.size = 2 ^ level - 1 := by have := perfect.gaps; omega

/-- Only the connecting skeleton may be rearranged; block trees stay intact. -/
inductive Fragment (α : Type*)
  | block (level : Nat) (tree : RawTree α) (perfect : Perfect level tree)
  | node (left : Fragment α) (key : α) (right : Fragment α)

namespace Fragment

def marked : Fragment α → MarkedTree α
  | .block _ tree _ => .hole tree
  | .node left key right => .node left.marked key right.marked

def levels : Fragment α → List Nat
  | .block level _ _ => [level]
  | .node left _ right => left.levels ++ right.levels

theorem levels_length (fragment : Fragment α) :
    fragment.levels.length = fragment.marked.skeleton.size + 1 := by
  induction fragment with
  | block => rfl
  | node left key right ihl ihr =>
      simp only [levels, marked, MarkedTree.skeleton, Tree.size, List.length_append]
      omega

theorem weight_eq (fragment : Fragment α) :
    Dyadic.weight fragment.levels = fragment.marked.erase.size + 1 := by
  induction fragment with
  | block level tree perfect =>
      simpa [levels, marked, MarkedTree.erase] using perfect.gaps.symm
  | node left key right ihl ihr =>
      simp only [levels, marked, MarkedTree.erase, Tree.size, Dyadic.weight_append, ihl, ihr]
      omega

theorem credit_eq (fragment : Fragment α) :
    Dyadic.credit fragment.levels + fragment.marked.skeleton.size = fragment.marked.erase.size := by
  have complete := Dyadic.credit_exact fragment.levels
  rw [fragment.levels_length, fragment.weight_eq] at complete
  omega

end Fragment

/-- The complete witness includes both the actual marked path and its
dyadic accounting. No existence or cost property is assumed later. -/
structure BlockCut (level : Nat) (tree : RawTree α) (key : α) where
  left : Fragment α
  right : Fragment α
  source : MarkedTree α
  steps : Nat
  source_tree : source.erase = tree
  same_holes : source.holes = left.marked.holes ++ right.marked.holes
  same_keys : source.skeleton.inorder =
    left.marked.skeleton.inorder ++ [key] ++ right.marked.skeleton.inorder
  source_size : source.skeleton.size = steps
  dyadic : Dyadic.Cut level left.levels right.levels steps

theorem Perfect.cut_exists {level : Nat} {tree : RawTree α} (perfect : Perfect level tree)
    (key : α) (inside : key ∈ tree.inorder) : Nonempty (BlockCut level tree key) := by
  induction perfect with
  | empty => simp [Tree.inorder] at inside
  | @node level left right pivot first last ihl ihr =>
      simp only [Tree.inorder, List.mem_append, List.mem_singleton] at inside
      rcases inside with (inLeft | atRoot) | inRight
      · obtain ⟨cut⟩ := ihl inLeft
        refine ⟨{
          left := cut.left
          right := .node cut.right pivot (.block level right last)
          source := .node cut.source pivot (.hole right)
          steps := cut.steps + 1
          source_tree := ?_
          same_holes := ?_
          same_keys := ?_
          source_size := ?_
          dyadic := ?_ }⟩
        · simp only [MarkedTree.erase, cut.source_tree]
        · simpa only [MarkedTree.holes, Fragment.marked, cut.same_holes,
            List.append_assoc]
        · simpa only [MarkedTree.skeleton, Tree.inorder, Fragment.marked, cut.same_keys,
            List.append_assoc, List.append_nil]
        · simp [MarkedTree.skeleton, Tree.size, cut.source_size]
        · exact .left cut.dyadic
      · subst key
        exact ⟨{
          left := .block level left first
          right := .block level right last
          source := .node (.hole left) pivot (.hole right)
          steps := 1
          source_tree := rfl
          same_holes := rfl
          same_keys := rfl
          source_size := rfl
          dyadic := .root level }⟩
      · obtain ⟨cut⟩ := ihr inRight
        refine ⟨{
          left := .node (.block level left first) pivot cut.left
          right := cut.right
          source := .node (.hole left) pivot cut.source
          steps := cut.steps + 1
          source_tree := ?_
          same_holes := ?_
          same_keys := ?_
          source_size := ?_
          dyadic := ?_ }⟩
        · simp only [MarkedTree.erase, cut.source_tree]
        · simpa only [MarkedTree.holes, Fragment.marked, cut.same_holes,
            List.append_assoc]
        · simpa only [MarkedTree.skeleton, Tree.inorder, Fragment.marked, cut.same_keys,
            List.append_assoc, List.nil_append]
        · simp [MarkedTree.skeleton, Tree.size, cut.source_size]
          omega
        · exact .right cut.dyadic

namespace BlockCut

def target {level : Nat} {tree : RawTree α} {key : α}
    (cut : BlockCut level tree key) : MarkedTree α :=
  .node cut.left.marked key cut.right.marked

def hull {level : Nat} {tree : RawTree α} {key : α}
    (cut : BlockCut level tree key) :
    HullStep key tree (.node cut.left.marked.erase key cut.right.marked.erase) where
  source := cut.source.skeleton
  target := cut.target.skeleton
  gaps := cut.source.gapArray
  source_tree := cut.source.graft_gapArray.trans cut.source_tree
  target_tree := by
    have gaps : cut.source.gapArray = cut.target.gapArray := by
      funext index
      simp only [MarkedTree.gapArray, target, MarkedTree.holes, cut.same_holes]
    rw [gaps, cut.target.graft_gapArray]
    rfl
  same_keys := cut.same_keys
  target_root := rfl

theorem hull_cost {level : Nat} {tree : RawTree α} {key : α}
    (cut : BlockCut level tree key) : cut.hull.cost = cut.steps := cut.source_size

theorem rotations {level : Nat} {tree : RawTree Nat} {key : Nat}
    (cut : BlockCut level tree key) :
    ∃ count ≤ 6 * cut.steps, SearchRotation.Rotations tree
      (.node cut.left.marked.erase key cut.right.marked.erase) count := by
  obtain ⟨count, bound, run⟩ := cut.hull.shallow_simulation
  exact ⟨count, by simpa only [cut.hull_cost] using bound,
    OnlineModel.restrictedSteps_to_rotations run⟩

theorem credits {level : Nat} {tree : RawTree α} {key : α}
    (cut : BlockCut level tree key) :
    Dyadic.credit cut.left.levels + Dyadic.credit cut.right.levels + cut.steps = tree.size := by
  have accounting := cut.dyadic.credits
  have physical := cut.dyadic.weights
  rw [cut.left.weight_eq, cut.right.weight_eq] at physical
  have sameSize : tree.size = cut.left.marked.erase.size + 1 + cut.right.marked.erase.size := by
    obtain ⟨count, bound, run⟩ := cut.hull.shallow_simulation
    exact run.size_eq
  omega

end BlockCut

end DynamicOptimality.GeometricOnlineSimulation

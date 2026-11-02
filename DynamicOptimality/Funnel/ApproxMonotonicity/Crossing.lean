import DynamicOptimality.Funnel.ApproxMonotonicity.Paths

/-! # Crossing depth with an explicit terminal marker

A Boolean labels each proper search ancestor by its side of the target.
`none` is a distinct terminal marker, including for an insertion search.
Thus a root search has crossing depth one; every other search has its
number of side changes plus two. The incoming boundary direction is used
only to compare two subtrees inside the same larger tree.
-/

namespace DynamicOptimality.Funnel.ApproxMonotonicity

open ChaCha.MTR ChaCha.MTR.Tree Warm

variable {α : Type*} [LinearOrder α]

def crossingFrom (boundary : Option Bool) (x : α) (tree : Tree α) : Nat :=
  changesFrom (boundary.map some) ((sidePath x tree).map some ++ [none])

def crossingDepth (x : α) (tree : Tree α) : Nat := crossingFrom none x tree + 1

private theorem append_cons_changes {β : Type*} [DecidableEq β]
    (previous : Option β) (p : List β) (a : β) (tail : List β) :
    changesFrom previous (p ++ a :: tail) =
      changesFrom previous (p ++ [a]) + changesFrom (some a) tail := by
  induction p generalizing previous with
  | nil => simp [changesFrom]
  | cons b p ih => simp [changesFrom,ih,Nat.add_assoc]

private theorem append_pair_changes {β : Type*} [DecidableEq β]
    (previous : Option β) (p : List β) (a b : β) (tail : List β) :
    changesFrom previous (p ++ a :: b :: tail) =
      changesFrom previous (p ++ [a,b]) + changesFrom (some b) tail := by
  induction p generalizing previous with
  | nil => simp [changesFrom,Nat.add_assoc]
  | cons c p ih => simp [changesFrom,ih,Nat.add_assoc]

private theorem head_append_cons_changes {β : Type*} [DecidableEq β]
    (previous : Option β) (a : β) (p : List β) (b : β) (tail : List β) :
    changesFrom previous (a :: (p ++ b :: tail)) =
      changesFrom previous (a :: (p ++ [b])) + changesFrom (some b) tail := by
  simp only [changesFrom]
  rw [append_cons_changes]
  omega

private theorem insert_suffix {β : Type*} [DecidableEq β]
    (previous : Option β) (p : List β) (a : β) (tail : List β) :
    changesFrom previous (p ++ tail) ≤ changesFrom previous (p ++ a :: tail) := by
  induction p generalizing previous with
  | nil => simpa [changesFrom] using changesFrom_triangle previous a tail
  | cons b p ih => simpa [changesFrom] using Nat.add_le_add_left (ih (some b)) (changeStep previous b)

private theorem splitPaths_bound (boundary : Option Bool) {a b c d : List Bool}
    (split : SplitPaths a b c d) :
    changesFrom (boundary.map some) (a.map some ++ [none]) +
      4 * changes (d.map some ++ [none]) ≤
    changesFrom (boundary.map some) (some true :: c.map some ++ [none]) +
      4 * changes (b.map some ++ [none]) := by
  induction split with
  | absent p =>
    have bound := prefix_lower boundary p none
    have insert := insert_suffix (boundary.map some) (p.map some) (some true) [none]
    omega
  | lower p xs =>
    cases xs with
    | nil => simpa using prefix_lower boundary p none
    | cons s xs =>
      have bound := prefix_lower boundary p (some s)
      simp only [List.map_append,List.map_cons,List.append_assoc,List.cons_append] at *
      rw [append_pair_changes _ (p.map some) (some true) (some s),
        head_append_cons_changes _ (some true) ((p.filter (! ·)).map some) (some s)]
      omega
  | upper p ys =>
    cases ys with
    | nil => simpa using prefix_upper boundary p none
    | cons s ys =>
      have bound := prefix_upper boundary p (some s)
      simp only [List.map_append,List.map_cons,List.append_assoc,List.cons_append] at *
      rw [show changes ((p.filter id).map some ++ some s :: (ys.map some ++ [none])) =
          changes ((p.filter id).map some ++ [some s]) +
            changesFrom (some (some s)) (ys.map some ++ [none]) from
          append_cons_changes _ _ _ _,
        show changes (p.map some ++ some false :: some s :: (ys.map some ++ [none])) =
          changes (p.map some ++ [some false,some s]) +
            changesFrom (some (some s)) (ys.map some ++ [none]) from
          append_pair_changes _ (p.map some) _ _ _]
      omega
  | fork p xs ys =>
    have bound := prefix_fork boundary p
    simp only [List.map_append,List.map_cons,List.append_assoc,List.cons_append] at bound ⊢
    rw [append_cons_changes _ (p.map some) (some true),
      show changes ((p.filter id).map some ++ some false :: (ys.map some ++ [none])) =
        changes ((p.filter id).map some ++ [some false]) +
          changesFrom (some (some false)) (ys.map some ++ [none]) from
        append_cons_changes _ _ _ _,
      head_append_cons_changes _ (some true) ((p.filter (! ·)).map some) (some true),
      show changes (p.map some ++ some false :: (ys.map some ++ [none])) =
        changes (p.map some ++ [some false]) +
          changesFrom (some (some false)) (ys.map some ++ [none]) from
        append_cons_changes _ _ _ _]
    omega

/-- The local amortized comparison when the promoted key is smaller than
the current request. The remaining distinguished interval is the lower part. -/
theorem local_below (boundary : Option Bool) (tree : Tree α) (ordered : Ordered tree)
    (x y : α) (yx : y < x) :
    crossingFrom boundary x tree + 4 * crossingDepth y (below x tree) ≤
      crossingFrom boundary x (access y tree) + 4 * crossingDepth y tree := by
  have bound := splitPaths_bound boundary (splitPaths tree ordered x y yx)
  have promoted := sidePath_right (below y tree) (above y tree) y x yx
  simp only [crossingFrom,crossingDepth,access,promoted,List.map_cons,changes,Option.map_none] at *
  omega

@[simp] theorem crossingFrom_empty (boundary : Option Bool) (x : α) :
    crossingFrom boundary x (.empty : Tree α) = changeStep (boundary.map some) none := by
  simp [crossingFrom,changesFrom]

@[simp] theorem crossingFrom_root (boundary : Option Bool) (l r : Tree α) (x : α) :
    crossingFrom boundary x (.node l x r) = changeStep (boundary.map some) none := by
  simp [crossingFrom,changesFrom]

theorem crossingFrom_left (boundary : Option Bool) (l r : Tree α) (a x : α) (xa : x < a) :
    crossingFrom boundary x (.node l a r) =
      changeStep (boundary.map some) (some false) + crossingFrom (some false) x l := by
  simp [crossingFrom,sidePath_left l r a x xa,changesFrom]

theorem crossingFrom_right (boundary : Option Bool) (l r : Tree α) (a x : α) (ax : a < x) :
    crossingFrom boundary x (.node l a r) =
      changeStep (boundary.map some) (some true) + crossingFrom (some true) x r := by
  simp [crossingFrom,sidePath_right l r a x ax,changesFrom]

theorem crossingFrom_le (boundary : Option Bool) (x : α) (tree : Tree α) :
    crossingFrom boundary x tree ≤ crossingDepth x tree := by
  cases boundary with
  | none => simp [crossingDepth]
  | some b =>
    cases path : (sidePath x tree).map some ++ [none] with
    | nil => simp [crossingFrom,path,crossingDepth,changesFrom]
    | cons a rest =>
      have first := changeStep_le (some (some b)) a
      simp only [crossingFrom,crossingDepth,path,Option.map_some,changesFrom,changeStep] at *
      omega

/-- Querying the promoted key removes the entire distinguished interval. -/
theorem local_equal (boundary : Option Bool) (tree : Tree α) (x : α) :
    crossingFrom boundary x tree ≤
      crossingFrom boundary x (access x tree) + 4 * crossingDepth x tree := by
  have bound := crossingFrom_le boundary x tree
  omega

end DynamicOptimality.Funnel.ApproxMonotonicity

import ChaCha.ColoredMerge

/-!
# Colored primary merging on arbitrary binary partition trees

The tree need not be perfect or have uniform leaf depths.  Every internal
node stores its actual binary partition predicate; its child words are
the corresponding filtered words.  The local four-symbol inequality
telescopes on this concrete recursive count.
-/

namespace ChaCha.GenericPartitionMerge

inductive PartitionTree (α : Type*) where
  | leaf
  | split (branch : α → Bool) (left right : PartitionTree α)

abbrev Occurrence (α : Type*) := Bool × α

def byColor (c : Bool) (xs : List (Occurrence α)) : List (Occurrence α) :=
  xs.filter (fun x => x.1 == c)

def child (branch : α → Bool) (d : Bool)
    (xs : List (Occurrence α)) : List (Occurrence α) :=
  xs.filter (fun x => branch x.2 == d)

def pairs (branch : α → Bool) (xs : List (Occurrence α)) :
    List ColoredMerge.Symbol := xs.map (fun x => (x.1, branch x.2))

def cyclicCost : PartitionTree α → List (Occurrence α) → Nat
  | .leaf, _ => 0
  | .split branch left right, xs =>
      cyclicAlternations (xs.map (fun x => branch x.2)) +
        cyclicCost left (child branch false xs) +
        cyclicCost right (child branch true xs)

theorem pairs_colors (branch : α → Bool) (xs : List (Occurrence α)) :
    (pairs branch xs).map Prod.fst = xs.map Prod.fst := by
  simp [pairs, List.map_map]

theorem pairs_directions (branch : α → Bool) (xs : List (Occurrence α)) :
    (pairs branch xs).map Prod.snd = xs.map (fun x => branch x.2) := by
  simp [pairs, List.map_map]

theorem child_colors (branch : α → Bool) (d : Bool)
    (xs : List (Occurrence α)) :
    (child branch d xs).map Prod.fst = ColoredMerge.byD d (pairs branch xs) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rcases x with ⟨c, key⟩
    cases hb : branch key <;> cases d <;>
      simp_all [child, pairs, ColoredMerge.byD]

theorem color_directions (branch : α → Bool) (c : Bool)
    (xs : List (Occurrence α)) :
    (byColor c xs).map (fun x => branch x.2) =
      ColoredMerge.byC c (pairs branch xs) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rcases x with ⟨xc, key⟩
    cases c <;> cases xc <;>
      simp_all [byColor, pairs, ColoredMerge.byC]

theorem child_byColor (branch : α → Bool) (c d : Bool)
    (xs : List (Occurrence α)) :
    child branch d (byColor c xs) = byColor c (child branch d xs) := by
  simp only [child, byColor, List.filter_filter]
  congr 1
  funext x
  exact Bool.and_comm _ _

/-- Arbitrary binary classifiers and arbitrary occurrence colors, including
overlapping color supports, satisfy the same cyclic merge inequality. -/
theorem cyclicCost_merge (tree : PartitionTree α) (xs : List (Occurrence α)) :
    cyclicCost tree xs ≤
      3 * cyclicCost tree (byColor false xs) +
      3 * cyclicCost tree (byColor true xs) +
      cyclicAlternations (xs.map Prod.fst) := by
  induction tree generalizing xs with
  | leaf => simp [cyclicCost]
  | split branch left right ihl ihr =>
    have hl := ihl (child branch false xs)
    have hr := ihr (child branch true xs)
    have hroot := ColoredMerge.cyclic_four_symbol (pairs branch xs)
    rw [pairs_colors, pairs_directions] at hroot
    rw [← child_colors branch false xs, ← child_colors branch true xs,
      ← color_directions branch false xs,
      ← color_directions branch true xs] at hroot
    simp only [cyclicCost, child_byColor]
    omega

theorem cyclicCost_merge_length (tree : PartitionTree α)
    (xs : List (Occurrence α)) :
    cyclicCost tree xs ≤
      3 * cyclicCost tree (byColor false xs) +
      3 * cyclicCost tree (byColor true xs) + xs.length := by
  have hm := cyclicCost_merge tree xs
  have hc := ColoredMerge.cyclicAlternations_le_length (xs.map Prod.fst)
  simp only [List.length_map] at hc
  omega

end ChaCha.GenericPartitionMerge

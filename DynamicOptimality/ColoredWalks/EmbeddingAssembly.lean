import DynamicOptimality.ColoredWalks.EmbeddingOrder

/-! # Filling the gaps of a small exposed skeleton

The skeleton contains the first and last key of each color in the current
interval. Its holes contain recursively constructed trees. When a neighbor
pair separates at a skeleton node, each endpoint is an extreme of its
child interval; the recursive root-depth invariant then bounds the actual
path between them. Pairs inside one hole keep their recursive distance.
-/

namespace DynamicOptimality.ColoredWalks

open ChaCha.MTR

variable {α β : Type*} [LinearOrder α]

def assemble (fill : List α → RawTree α) : RawTree α → List α → RawTree α
  | .empty, keys => fill keys
  | .node left pivot right, keys =>
      .node (assemble fill left (lowerKeys keys pivot)) pivot (assemble fill right (upperKeys keys pivot))

def AllGaps (predicate : List α → Prop) : RawTree α → List α → Prop
  | .empty, keys => predicate keys
  | .node left pivot right, keys =>
      AllGaps predicate left (lowerKeys keys pivot) ∧ AllGaps predicate right (upperKeys keys pivot)

theorem AllGaps.mono {P Q : List α → Prop} {skeleton : RawTree α} {keys : List α}
    (gaps : AllGaps P skeleton keys) (implication : ∀ part, P part → Q part) :
    AllGaps Q skeleton keys := by
  induction skeleton generalizing keys with
  | empty => exact implication keys gaps
  | node left pivot right leftIH rightIH => exact ⟨leftIH gaps.1,rightIH gaps.2⟩

theorem allGaps_of_sublist (P : List α → Prop) (skeleton : RawTree α) (keys : List α)
    (all : ∀ part, part.Sublist keys → P part) : AllGaps P skeleton keys := by
  induction skeleton generalizing keys with
  | empty => exact all keys (List.Sublist.refl keys)
  | node left pivot right leftIH rightIH =>
    exact ⟨leftIH _ (fun part inside => all part (inside.trans (lowerKeys_sublist keys pivot))),
      rightIH _ (fun part inside => all part (inside.trans (upperKeys_sublist keys pivot)))⟩

/-- Every actual gap loses at least the exposed root of a nonempty skeleton. -/
theorem allGaps_shorter {skeleton : RawTree α} {keys : List α}
    (ordered : keys.Pairwise (· < ·)) (nonempty : skeleton ≠ .empty)
    (covered : ∀ key ∈ skeleton.inorder, key ∈ keys) :
    AllGaps (fun part => part.Sublist keys ∧ part.length < keys.length) skeleton keys := by
  cases skeleton with
  | empty => exact (nonempty rfl).elim
  | node left pivot right =>
    have pivotMember := covered pivot (by simp [Tree.inorder])
    constructor
    · apply allGaps_of_sublist
      intro part inside
      exact ⟨inside.trans (lowerKeys_sublist keys pivot),
        inside.length_le.trans_lt (lowerKeys_shorter ordered pivotMember)⟩
    · apply allGaps_of_sublist
      intro part inside
      exact ⟨inside.trans (upperKeys_sublist keys pivot),
        inside.length_le.trans_lt (upperKeys_shorter ordered pivotMember)⟩

theorem assemble_word (fill : List α → RawTree α) {skeleton : RawTree α} {keys : List α}
    (ordered : keys.Pairwise (· < ·)) (skeletonOrdered : skeleton.Ordered)
    (covered : ∀ key ∈ skeleton.inorder, key ∈ keys)
    (gaps : AllGaps (fun part => (fill part).inorder = part) skeleton keys) :
    (assemble fill skeleton keys).inorder = keys := by
  induction skeleton generalizing keys with
  | empty => exact gaps
  | node left pivot right leftIH rightIH =>
    obtain ⟨leftOrdered,rightOrdered,below,above⟩ := ordered_node skeletonOrdered
    have leftCovered : ∀ key ∈ left.inorder, key ∈ lowerKeys keys pivot := by
      intro key member
      exact mem_lowerKeys.mpr ⟨covered key (by simp [Tree.inorder,member]),below key member⟩
    have rightCovered : ∀ key ∈ right.inorder, key ∈ upperKeys keys pivot := by
      intro key member
      exact mem_upperKeys.mpr ⟨covered key (by simp [Tree.inorder,member]),above key member⟩
    simp only [assemble,Tree.inorder,
      leftIH (lowerKeys_ordered ordered pivot) leftOrdered leftCovered gaps.1,
      rightIH (upperKeys_ordered ordered pivot) rightOrdered rightCovered gaps.2]
    exact split_keys ordered (covered pivot (by simp [Tree.inorder]))

/-- Grafting a recursive tree into a null child does not move exposed keys. -/
theorem RootPath.assemble (fill : List α → RawTree α) {skeleton : RawTree α} {key : α} {depth : Nat}
    (path : RootPath skeleton key depth) (keys : List α) : RootPath (assemble fill skeleton keys) key depth := by
  induction path generalizing keys with
  | root left key right => exact .root _ _ _
  | left _ parent right ih => exact .left (ih _) parent _
  | right left parent _ ih => exact .right _ parent (ih _)

theorem assemble_extreme (fill : List α → RawTree α) (color : α → β) (height : Nat)
    {skeleton : RawTree α} {keys : List α}
    (gaps : AllGaps (fun part => Embedding color part height (fill part)) skeleton keys)
    {key : α} (extreme : Extreme color keys key) :
    ∃ depth, RootPath (assemble fill skeleton keys) key depth ∧ depth < treeHeight skeleton+height := by
  induction skeleton generalizing keys with
  | empty => simpa only [assemble,treeHeight,Nat.zero_add] using gaps.extreme key extreme
  | node left pivot right leftIH rightIH =>
    rcases lt_trichotomy key pivot with below | same | above
    · have localExtreme := extreme.restrict (lowerKeys_subset keys pivot) (mem_lowerKeys.mpr ⟨extreme.1,below⟩)
      obtain ⟨depth,path,small⟩ := leftIH gaps.1 localExtreme
      refine ⟨depth+1,.left path pivot _,?_⟩
      simp only [treeHeight]
      omega
    · subst key
      exact ⟨0,.root _ _ _,by simp [treeHeight]⟩
    · have localExtreme := extreme.restrict (upperKeys_subset keys pivot) (mem_upperKeys.mpr ⟨extreme.1,above⟩)
      obtain ⟨depth,path,small⟩ := rightIH gaps.2 localExtreme
      refine ⟨depth+1,.right _ pivot path,?_⟩
      simp only [treeHeight]
      omega

theorem assemble_first_cross (fill : List α → RawTree α) (color : α → β) (height : Nat)
    {left right : RawTree α} {pivot : α} {keys : List α}
    (gaps : AllGaps (fun part => Embedding color part height (fill part)) (.node left pivot right) keys)
    {first last : α} (neighbors : Neighbors color keys first last)
    (firstSide : first ≤ pivot) (lastSide : pivot ≤ last) :
    ∃ depth, RootPath (assemble fill (.node left pivot right) keys) first depth ∧
      depth ≤ treeHeight (.node left pivot right)+height := by
  rcases lt_or_eq_of_le firstSide with below | same
  · have extreme := neighbors.first_extreme (lowerKeys_subset keys pivot)
      (mem_lowerKeys.mpr ⟨neighbors.first_mem,below⟩)
      (fun key member => ((mem_lowerKeys.mp member).2).trans_le lastSide)
    obtain ⟨depth,path,small⟩ := assemble_extreme fill color height gaps.1 extreme
    refine ⟨depth+1,.left path pivot _,?_⟩
    simp only [treeHeight]
    omega
  · subst first
    exact ⟨0,.root _ _ _,Nat.zero_le _⟩

theorem assemble_last_cross (fill : List α → RawTree α) (color : α → β) (height : Nat)
    {left right : RawTree α} {pivot : α} {keys : List α}
    (gaps : AllGaps (fun part => Embedding color part height (fill part)) (.node left pivot right) keys)
    {first last : α} (neighbors : Neighbors color keys first last)
    (firstSide : first ≤ pivot) (lastSide : pivot ≤ last) :
    ∃ depth, RootPath (assemble fill (.node left pivot right) keys) last depth ∧
      depth ≤ treeHeight (.node left pivot right)+height := by
  rcases lt_or_eq_of_le lastSide with above | same
  · have extreme := neighbors.last_extreme (upperKeys_subset keys pivot)
      (mem_upperKeys.mpr ⟨neighbors.last_mem,above⟩)
      (fun key member => firstSide.trans_lt (mem_upperKeys.mp member).2)
    obtain ⟨depth,path,small⟩ := assemble_extreme fill color height gaps.2 extreme
    refine ⟨depth+1,.right _ pivot path,?_⟩
    simp only [treeHeight]
    omega
  · subst last
    exact ⟨0,.root _ _ _,Nat.zero_le _⟩

theorem assemble_neighbors (fill : List α → RawTree α) (color : α → β) (height : Nat)
    {skeleton : RawTree α} {keys : List α}
    (gaps : AllGaps (fun part => Embedding color part height (fill part)) skeleton keys)
    (small : treeHeight skeleton ≤ height) {first last : α}
    (neighbors : Neighbors color keys first last) :
    DistanceLE (assemble fill skeleton keys) first last (4*height) := by
  induction skeleton generalizing keys with
  | empty => exact gaps.neighbors first last neighbors
  | node left pivot right leftIH rightIH =>
    by_cases below : last < pivot
    · have inside := neighbors.restrict (lowerKeys_subset keys pivot)
        (mem_lowerKeys.mpr ⟨neighbors.first_mem,neighbors.increasing.trans below⟩)
        (mem_lowerKeys.mpr ⟨neighbors.last_mem,below⟩)
      exact .left (leftIH gaps.1 (by simp only [treeHeight] at small; omega) inside) pivot _
    · by_cases above : pivot < first
      · have inside := neighbors.restrict (upperKeys_subset keys pivot)
          (mem_upperKeys.mpr ⟨neighbors.first_mem,above⟩)
          (mem_upperKeys.mpr ⟨neighbors.last_mem,above.trans neighbors.increasing⟩)
        exact .right _ pivot (rightIH gaps.2 (by simp only [treeHeight] at small; omega) inside)
      · have firstSide := le_of_not_gt above
        have lastSide := le_of_not_gt below
        obtain ⟨a,firstPath,firstSmall⟩ := assemble_first_cross fill color height gaps neighbors firstSide lastSide
        obtain ⟨b,lastPath,lastSmall⟩ := assemble_last_cross fill color height gaps neighbors firstSide lastSide
        exact .viaRoot firstPath lastPath (by omega)

end DynamicOptimality.ColoredWalks

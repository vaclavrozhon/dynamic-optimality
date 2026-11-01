import SparseActiveTree
import HistoricalKeyCuts
import Greedy.SignedCuts

/-!
# Cancellation inside one consecutive source block

The search path to a cut becomes trapped between the endpoints of any
crossing edge. Hence, once both endpoints of a crossing belong to a key
interval, all later path vertices belong to it. Keeping exactly the
internal edges therefore preserves cancellation. No condition on labels
is imposed: equal-label edges must be kept as well.
-/

namespace Greedy.IntervalCancellation

open GreedyForest.ActiveTree GreedyForest.HistoricalCuts

def side (cut key : ℕ) : ℤ := if cut ≤ key then 1 else 0

def internalWeight (cut lo hi parent child : ℕ) : ℤ :=
  if lo ≤ parent ∧ parent ≤ hi ∧ lo ≤ child ∧ child ≤ hi
    then side cut child - side cut parent else 0

def headWeight (cut lo hi parent : ℕ) : List ℕ → ℤ
  | [] => 0
  | child :: _ => internalWeight cut lo hi parent child

def pathSum (cut lo hi : ℕ) : List ℕ → ℤ
  | [] => 0
  | parent :: rest => headWeight cut lo hi parent rest + pathSum cut lo hi rest

def Trapped (cut : ℕ) : List ℕ → Prop
  | [] => True
  | parent :: rest => Trapped cut rest ∧
      ∀ child tail, rest = child :: tail → KeyCrosses cut parent child →
        ∀ key ∈ tail, min parent child ≤ key ∧ key ≤ max parent child

theorem side_bounds (cut key : ℕ) : 0 ≤ side cut key ∧ side cut key ≤ 1 := by
  unfold side
  split_ifs <;> omega

theorem side_eq_of_not_crossing (cut a b : ℕ) (same : ¬ KeyCrosses cut a b) :
    side cut a = side cut b := by
  unfold side KeyCrosses at *
  split_ifs <;> omega

theorem full_path_bounds (cut lo hi parent : ℕ) (rest : List ℕ)
    (inside : ∀ key ∈ parent :: rest, lo ≤ key ∧ key ≤ hi) :
    0 ≤ pathSum cut lo hi (parent :: rest) + side cut parent ∧
      pathSum cut lo hi (parent :: rest) + side cut parent ≤ 1 := by
  induction rest generalizing parent with
  | nil => simpa [pathSum, headWeight] using side_bounds cut parent
  | cons child tail ih =>
      have parentIn := inside parent (by simp)
      have childIn := inside child (by simp)
      have tailIn : ∀ key ∈ child :: tail, lo ≤ key ∧ key ≤ hi := by
        intro key member
        exact inside key (List.mem_cons_of_mem parent member)
      have bound := ih child tailIn
      change 0 ≤ internalWeight cut lo hi parent child +
          pathSum cut lo hi (child :: tail) + side cut parent ∧ _
      have edgeEq : internalWeight cut lo hi parent child = side cut child - side cut parent := by
        simp [internalWeight, parentIn.1, parentIn.2, childIn.1, childIn.2]
      change 0 ≤ internalWeight cut lo hi parent child +
          pathSum cut lo hi (child :: tail) + side cut parent ∧
        internalWeight cut lo hi parent child +
          pathSum cut lo hi (child :: tail) + side cut parent ≤ 1
      rw [edgeEq]
      omega

theorem full_path_abs (cut lo hi : ℕ) (path : List ℕ)
    (inside : ∀ key ∈ path, lo ≤ key ∧ key ≤ hi) : |pathSum cut lo hi path| ≤ 1 := by
  cases path with
  | nil => simp [pathSum]
  | cons parent rest =>
      have bound := full_path_bounds cut lo hi parent rest inside
      have bitBound := side_bounds cut parent
      rw [abs_le]
      omega

theorem trapped_path_abs (cut lo hi : ℕ) (path : List ℕ) (trapped : Trapped cut path) :
    |pathSum cut lo hi path| ≤ 1 := by
  induction path with
  | nil => simp [pathSum]
  | cons parent rest ih =>
      have tailBound := ih trapped.1
      cases rest with
      | nil => simp [pathSum, headWeight]
      | cons child tail =>
          by_cases inside : lo ≤ parent ∧ parent ≤ hi ∧ lo ≤ child ∧ child ≤ hi
          · by_cases crossing : KeyCrosses cut parent child
            · apply full_path_abs
              intro key member
              rcases List.mem_cons.mp member with rfl | member
              · exact ⟨inside.1, inside.2.1⟩
              · rcases List.mem_cons.mp member with rfl | member
                · exact inside.2.2
                · have bounds := trapped.2 child tail rfl crossing key member
                  omega
            · have same := side_eq_of_not_crossing cut parent child crossing
              simpa only [pathSum, headWeight, internalWeight, if_pos inside, same,
                sub_self, zero_add] using tailBound
          · simpa only [pathSum, headWeight, internalWeight, if_neg inside, zero_add] using tailBound

def cutPath (cut : ℕ) : Sparse → List ℕ
  | .empty => []
  | .node key left right =>
      key :: if key < cut then cutPath cut right else cutPath cut left

theorem cutPath_mem (cut : ℕ) (tree : Sparse) :
    ∀ key ∈ cutPath cut tree, key ∈ tree.keys := by
  induction tree with
  | empty => simp [cutPath]
  | node root left right il ir =>
      intro key member
      simp only [cutPath, List.mem_cons] at member
      rcases member with rfl | member
      · exact Sparse.root_mem _ _ _
      · split_ifs at member with h
        · have childMem := ir key member
          simp [Sparse.keys, childMem]
        · have childMem := il key member
          simp [Sparse.keys, childMem]

/-- Trapping follows from ordinary BST ordering, including sparse key
sets with arbitrary deletion holes. -/
theorem cutPath_trapped (cut : ℕ) (tree : Sparse) (ordered : tree.Ordered) :
    Trapped cut (cutPath cut tree) := by
  induction tree with
  | empty => trivial
  | node parent left right il ir =>
      by_cases parentLeft : parent < cut
      · simp only [cutPath, if_pos parentLeft, Trapped]
        refine ⟨ir ordered.2.1, ?_⟩
        intro child tail equality crossing key member
        cases right with
        | empty => simp [cutPath] at equality
        | node root l r =>
            have rootEq : root = child := (List.cons.inj equality).1
            subst root
            have childRight : ¬ child < cut := by unfold KeyCrosses at crossing; omega
            have tailEq : tail = cutPath cut l := by
              simpa only [cutPath, if_neg childRight, List.cons.injEq, true_and] using equality.symm
            have inLeft := cutPath_mem cut l key (tailEq ▸ member)
            have below := ordered.2.1.2.2.1 key inLeft
            have inRight : key ∈ (Sparse.node child l r).keys := by simp [Sparse.keys, inLeft]
            have above := ordered.2.2.2 key inRight
            omega
      · simp only [cutPath, if_neg parentLeft, Trapped]
        refine ⟨il ordered.1, ?_⟩
        intro child tail equality crossing key member
        cases left with
        | empty => simp [cutPath] at equality
        | node root l r =>
            have rootEq : root = child := (List.cons.inj equality).1
            subst root
            have childLeft : child < cut := by unfold KeyCrosses at crossing; omega
            have tailEq : tail = cutPath cut r := by
              simpa only [cutPath, if_pos childLeft, List.cons.injEq, true_and] using equality.symm
            have inRight := cutPath_mem cut r key (tailEq ▸ member)
            have above := ordered.1.2.2.2 key inRight
            have inLeft : key ∈ (Sparse.node child l r).keys := by simp [Sparse.keys, inRight]
            have below := ordered.2.2.1 key inLeft
            omega

theorem internal_cut_path_abs (cut lo hi : ℕ) (tree : Sparse) (ordered : tree.Ordered) :
    |pathSum cut lo hi (cutPath cut tree)| ≤ 1 :=
  trapped_path_abs cut lo hi _ (cutPath_trapped cut tree ordered)

end Greedy.IntervalCancellation

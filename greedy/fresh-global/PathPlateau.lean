import SearchGaps
import SurfaceHierarchy

/-!
Enumerate an actual old search path in key order and extract all its exact
original off-path subtrees in the intervening gaps. This is concrete typed
fringe data, independent of comparator ranks and surface heights.
-/
namespace GreedyMerge.PathPlateau
open Splay.Tree
open Splay.Tree.BST
open GreedyMerge.SearchGaps
open GreedyMerge.ExpansionRotations
open GreedyMerge.HierarchyExistence
open GreedyMerge.SurfaceHierarchy

structure Decomposition {n : ℕ} (tree : BST 0 n) (access : ℕ) where
  count : ℕ
  separator : ℕ → ℕ
  positive : 0 < count
  endpoint : separator count = n
  increasing : StrictMono separator
  tail : ∀ i, count ≤ i → separator i = separator count + (i - count)
  member : ∀ i, i < count → separator i ∈ PathKeys access tree
  complete : ∀ key, key ∈ PathKeys access tree → ∃ i, i < count ∧ key = separator i
  gaps : ∀ i, BST (GapLower 0 separator i) (separator i)
  actualGap : ∀ i, i ≤ count → SearchGap access (gaps i) tree

theorem exists_decomposition {n access : ℕ} (tree : BST 0 n) (haccess : access < n) :
    Nonempty (Decomposition tree access) := by
  classical
  have hnonempty : (PathKeys access tree).Nonempty := by
    cases tree with
    | empty => omega
    | node left right => exact ⟨_, root_mem_pathKeys left right⟩
  obtain ⟨count, separator, hcount, endpoint, increasing, first, tail, member, complete⟩ :=
    ordered_enumeration (PathKeys access tree) hnonempty
      (fun key hk => pathKeys_bounds tree hk)
  have gapOrder : ∀ i, GapLower 0 separator i ≤ separator i := by
    intro i
    cases i with
    | zero => exact Nat.zero_le _
    | succ i =>
        change separator i + 1 ≤ separator (i + 1)
        have h := increasing (show i < i + 1 by omega)
        omega
  have actualExists : ∀ i, i ≤ count → ∃ gap : BST (GapLower 0 separator i) (separator i),
      SearchGap access gap tree := by
    intro i hi
    have hupper : separator i ≤ n := by
      have h := increasing.monotone hi
      omega
    apply maximal_gap_is_subtree tree (Nat.zero_le access) haccess (Nat.zero_le _)
      (gapOrder i) hupper
    · intro key hklo hkhi hm
      obtain ⟨j, hj, heq⟩ := complete key hm
      have hji : j < i := increasing.lt_iff_lt.mp (heq ▸ hkhi)
      cases i with
      | zero => omega
      | succ i =>
          change separator i + 1 ≤ key at hklo
          have hij : i < j := increasing.lt_iff_lt.mp (by omega : separator i < separator j)
          omega
    · cases i with
      | zero => exact Or.inl rfl
      | succ i =>
          right
          simp only [GapLower, Nat.add_sub_cancel]
          exact member i (by omega)
    · by_cases heq : i = count
      · exact Or.inl (heq ▸ endpoint)
      · exact Or.inr (member i (by omega))
  let inside := fun i hi => Classical.choose (actualExists i hi)
  let gaps := completeGaps separator tail inside
  have hactual : ∀ i, i ≤ count → SearchGap access (gaps i) tree := by
    intro i hi
    dsimp only [gaps]
    rw [completeGaps_inside separator tail inside hi]
    exact Classical.choose_spec (actualExists i hi)
  exact ⟨⟨count, separator, hcount, endpoint, increasing, tail, member, complete, gaps, hactual⟩⟩

/-- Explicit endpoint transport needed because the enumerated final
separator is the universe boundary, not an additional real path key. -/
def castUpper {lo hi finish : ℕ} (equal : hi = finish) (tree : BST lo hi) : BST lo finish :=
  equal ▸ tree

def Decomposition.expand {n access : ℕ} {tree : BST 0 n} (p : Decomposition tree access)
    (skeleton : BST 0 p.count) : BST 0 n :=
  castUpper p.endpoint (Expand 0 p.separator p.gaps skeleton)

end GreedyMerge.PathPlateau
#print axioms GreedyMerge.PathPlateau.exists_decomposition

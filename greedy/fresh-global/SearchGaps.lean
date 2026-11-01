import SubtreeGap

/-!
Literal decomposition of an indexed BST search path into its ordered keys
and maximal off-path gap subtrees. Empty gap subtrees are retained.
-/
namespace GreedyMerge.SearchGaps
open Splay.Tree
open Splay.Tree.BST
open GreedyMerge.Surface

/-- Unordered key set of the ordinary successful search path. -/
def PathKeys (access : ℕ) {lo hi : ℕ} : BST lo hi → Finset ℕ
  | .empty _ => ∅
  | .node (root := root) left right =>
      if access = root then {root}
      else if access < root then insert root (PathKeys access left)
      else insert root (PathKeys access right)

theorem pathKeys_bounds {lo hi access key : ℕ} (tree : BST lo hi)
    (member : key ∈ PathKeys access tree) : lo ≤ key ∧ key < hi := by
  induction tree with
  | empty => simp [PathKeys] at member
  | @node lo root hi left right ihLeft ihRight =>
      have hl := left.lower_le_upper
      have hr := right.lower_le_upper
      simp only [PathKeys] at member
      split_ifs at member
      · simp only [Finset.mem_singleton] at member
        subst key
        omega
      · simp only [Finset.mem_insert] at member
        rcases member with rfl | hm
        · omega
        · have h := ihLeft hm; omega
      · simp only [Finset.mem_insert] at member
        rcases member with rfl | hm
        · omega
        · have h := ihRight hm; omega

theorem root_mem_pathKeys {lo root hi access : ℕ}
    (left : BST lo root) (right : BST (root + 1) hi) :
    root ∈ PathKeys access (.node left right) := by
  unfold PathKeys
  split_ifs <;> simp

theorem pathKeys_left_iff {lo root hi access key : ℕ}
    (left : BST lo root) (right : BST (root + 1) hi) (hk : key < root) :
    key ∈ PathKeys access (.node left right) ↔
      access < root ∧ key ∈ PathKeys access left := by
  by_cases heq : access = root
  · simp only [PathKeys, if_pos heq, Finset.mem_singleton]
    omega
  · by_cases hleft : access < root
    · simp [PathKeys, heq, hleft, ne_of_lt hk]
    · have hnot : key ∉ PathKeys access right := by
        intro hm
        have h := pathKeys_bounds right hm
        omega
      simp [PathKeys, heq, hleft, ne_of_lt hk, hnot]

theorem pathKeys_right_iff {lo root hi access key : ℕ}
    (left : BST lo root) (right : BST (root + 1) hi) (hk : root < key) :
    key ∈ PathKeys access (.node left right) ↔
      root < access ∧ key ∈ PathKeys access right := by
  by_cases heq : access = root
  · simp only [PathKeys, if_pos heq, Finset.mem_singleton]
    omega
  · by_cases hleft : access < root
    · have hnot : key ∉ PathKeys access left := by
        intro hm
        have h := pathKeys_bounds left hm
        omega
      simp [PathKeys, heq, hleft, ne_of_gt hk, hnot, show ¬root < access by omega]
    · have hright : root < access := by omega
      simp [PathKeys, heq, hleft, ne_of_gt hk, hright]

/-- A direct off-path branch of a node on the search path, possibly empty. -/
inductive SearchGap (access : ℕ) :
    {innerLo innerHi : ℕ} → BST innerLo innerHi → {lo hi : ℕ} → BST lo hi → Prop
  | leftGap {lo root hi : ℕ} (left : BST lo root) (right : BST (root + 1) hi)
      (outside : root ≤ access) : SearchGap access left (.node left right)
  | rightGap {lo root hi : ℕ} (left : BST lo root) (right : BST (root + 1) hi)
      (outside : access ≤ root) : SearchGap access right (.node left right)
  | left {innerLo innerHi lo root hi : ℕ} {inner : BST innerLo innerHi} {left : BST lo root} (right : BST (root + 1) hi)
      (direction : access < root) (inside : SearchGap access inner left) :
      SearchGap access inner (.node left right)
  | right {innerLo innerHi lo root hi : ℕ} {inner : BST innerLo innerHi} (left : BST lo root) {right : BST (root + 1) hi}
      (direction : root < access) (inside : SearchGap access inner right) :
      SearchGap access inner (.node left right)

theorem SearchGap.occurrence {access innerLo innerHi lo hi : ℕ}
    {inner : BST innerLo innerHi} {tree : BST lo hi} (gap : SearchGap access inner tree) :
    ∃ depth, SubtreeAt inner depth tree := by
  induction gap with
  | leftGap left right outside => exact ⟨1, .left .here right⟩
  | rightGap left right outside => exact ⟨1, .right left .here⟩
  | left right direction inside ih =>
      obtain ⟨depth, occurrence⟩ := ih
      exact ⟨depth + 1, .left occurrence right⟩
  | right left direction inside ih =>
      obtain ⟨depth, occurrence⟩ := ih
      exact ⟨depth + 1, .right left occurrence⟩

theorem SearchGap.outside {access innerLo innerHi lo hi : ℕ}
    {inner : BST innerLo innerHi} {tree : BST lo hi} (gap : SearchGap access inner tree) :
    access < innerLo ∨ innerHi ≤ access := by
  induction gap with
  | leftGap left right outside => exact Or.inr outside
  | rightGap left right outside => exact Or.inl (by omega)
  | left right direction inside ih => exact ih
  | right left direction inside ih => exact ih

/-- Every maximal interval between consecutive path keys is exactly one
literal off-path subtree, including empty intervals between adjacent keys. -/
theorem maximal_gap_is_subtree {lo hi first finish access : ℕ}
    (tree : BST lo hi) (haLo : lo ≤ access) (haHi : access < hi)
    (hfirst : lo ≤ first) (horder : first ≤ finish) (hfinish : finish ≤ hi)
    (none : ∀ key, first ≤ key → key < finish → key ∉ PathKeys access tree)
    (leftBoundary : first = lo ∨ first - 1 ∈ PathKeys access tree)
    (rightBoundary : finish = hi ∨ finish ∈ PathKeys access tree) :
    ∃ gap : BST first finish, SearchGap access gap tree := by
  induction tree with
  | empty => omega
  | @node lo root hi left right ihLeft ihRight =>
      have hl := left.lower_le_upper
      have hr := right.lower_le_upper
      have hroot := root_mem_pathKeys (access := access) left right
      have split : finish ≤ root ∨ root < first := by
        by_contra h
        exact none root (by omega) (by omega) hroot
      rcases split with htoLeft | htoRight
      · by_cases hsearch : access < root
        · have lb : first = lo ∨ first - 1 ∈ PathKeys access left := by
            rcases leftBoundary with heq | hm
            · exact Or.inl heq
            · right
              exact ((pathKeys_left_iff left right (by omega : first - 1 < root)).1 hm).2
          have rb : finish = root ∨ finish ∈ PathKeys access left := by
            by_cases heq : finish = root
            · exact Or.inl heq
            · right
              rcases rightBoundary with hh | hm
              · omega
              · exact ((pathKeys_left_iff left right (by omega : finish < root)).1 hm).2
          obtain ⟨gap, hgap⟩ := ihLeft haLo hsearch hfirst htoLeft
            (fun key hklo hkhi hm => none key hklo hkhi
              ((pathKeys_left_iff left right (by omega : key < root)).2 ⟨hsearch, hm⟩)) lb rb
          exact ⟨gap, .left right hsearch hgap⟩
        · have hfirstEq : first = lo := by
            by_contra hne
            rcases leftBoundary with heq | hm
            · exact hne heq
            · have hp := (pathKeys_left_iff left right (by omega : first - 1 < root)).1 hm
              omega
          have hfinishEq : finish = root := by
            by_contra hne
            rcases rightBoundary with heq | hm
            · omega
            · have hp := (pathKeys_left_iff left right (by omega : finish < root)).1 hm
              omega
          subst first
          subst finish
          exact ⟨left, .leftGap left right (by omega)⟩
      · by_cases hsearch : root < access
        · have lb : first = root + 1 ∨ first - 1 ∈ PathKeys access right := by
            by_cases heq : first = root + 1
            · exact Or.inl heq
            · right
              rcases leftBoundary with hh | hm
              · omega
              · exact ((pathKeys_right_iff left right (by omega : root < first - 1)).1 hm).2
          have rb : finish = hi ∨ finish ∈ PathKeys access right := by
            rcases rightBoundary with heq | hm
            · exact Or.inl heq
            · right
              exact ((pathKeys_right_iff left right (by omega : root < finish)).1 hm).2
          obtain ⟨gap, hgap⟩ := ihRight (by omega) haHi (by omega) hfinish
            (fun key hklo hkhi hm => none key hklo hkhi
              ((pathKeys_right_iff left right (by omega : root < key)).2 ⟨hsearch, hm⟩)) lb rb
          exact ⟨gap, .right left hsearch hgap⟩
        · have hfirstEq : first = root + 1 := by
            by_contra hne
            rcases leftBoundary with heq | hm
            · omega
            · have hp := (pathKeys_right_iff left right (by omega : root < first - 1)).1 hm
              omega
          have hfinishEq : finish = hi := by
            rcases rightBoundary with heq | hm
            · exact heq
            · have hp := (pathKeys_right_iff left right (by omega : root < finish)).1 hm
              omega
          subst first
          subst finish
          exact ⟨right, .rightGap left right (by omega)⟩


/-- Pointwise, rather than merely cardinal, correspondence between strict
neighborhood touches and the actual old refinement's search path. -/
theorem neighborhood_iff_pathKeys {n lo hi access key : ℕ}
    (height : ℕ → ℤ) (rank owner : ℕ → ℕ) (tree : BST lo hi)
    (owners : Owners height rank owner n)
    (global : UniqueGlobalMinimum rank n access)
    (exactOwners : ExactOwners rank owner tree) (hhi : hi ≤ n)
    (haLo : lo ≤ access) (haHi : access < hi)
    (hkLo : lo ≤ key) (hkHi : key < hi) :
    Neighborhood height n key access ↔ key ∈ PathKeys access tree := by
  induction tree generalizing key with
  | empty => omega
  | @node lo root hi left right ihLeft ihRight =>
      have hl := left.lower_le_upper
      have hr := right.lower_le_upper
      by_cases heq : key = root
      · subst key
        have howner : owner root = access :=
          (minimum_eq_iff_inside rank global (by omega) hhi exactOwners.1).2 ⟨haLo, haHi⟩
        have hvisible := (owner_eq_iff_neighborhood height rank owner owners global (by omega)).1 howner
        exact iff_of_true hvisible (root_mem_pathKeys left right)
      · by_cases hkLeft : key < root
        · rw [pathKeys_left_iff left right hkLeft]
          by_cases haLeft : access < root
          · have h := ihLeft exactOwners.2.1 (by omega) haLo haLeft hkLo hkLeft
            simpa only [haLeft, true_and] using h
          · have hnone := gap_has_no_touches height rank owner left owners global
              exactOwners.2.1 (by omega) (Or.inr (by omega)) key hkLo hkLeft
            simp [hnone, haLeft]
        · have hkRight : root < key := by omega
          rw [pathKeys_right_iff left right hkRight]
          by_cases haRight : root < access
          · have h := ihRight exactOwners.2.2 hhi (by omega) haHi (by omega) hkHi
            simpa only [haRight, true_and] using h
          · have hnone := gap_has_no_touches height rank owner right owners global
              exactOwners.2.2 hhi (Or.inl (by omega)) key (by omega) hkHi
            simp [hnone, haRight]

end GreedyMerge.SearchGaps
#print axioms GreedyMerge.SearchGaps.maximal_gap_is_subtree

#print axioms GreedyMerge.SearchGaps.neighborhood_iff_pathKeys

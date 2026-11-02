import MultiSplay.OrdinalEncoding
import MultiSplay.BoundedPreparation

/-! # Changing local ordinal coordinates preserves physical shape and geometry -/

namespace MultiSplay.Alphabet

open DynamicOptimality (RawTree)
open Splay.Tree (BST)
open ChaCha.MTR.Tree (inorder size)
open Splay.Accounting.OfflineNormalForm (leftBoundaryDepth rightBoundaryDepth HasBoundedMinorRibs)

variable {α : Type*}

theorem indexed_inorder {lower upper : Nat} (tree : BST lower upper) :
    inorder (DynamicOptimality.BST.toRaw tree) = List.range' lower tree.size := by
  apply (DynamicOptimality.BST.toRaw_ordered tree).eq_of_mem_iff (List.pairwise_lt_range')
  intro key
  rw [DynamicOptimality.BST.toRaw_mem, List.mem_range'_1]
  have count := tree.size_add_lower_eq_upper
  omega

/-- Within a fixed ordinal interval, the unlabeled physical shape determines
the indexed tree. The two external interpretations need not be injective. -/
theorem indexed_eq_of_map_eq {lower upper : Nat} (first second : BST lower upper)
    (a b : Nat → α)
    (same : Auxiliary.map a (DynamicOptimality.BST.toRaw first) = Auxiliary.map b (DynamicOptimality.BST.toRaw second)) :
    first = second := by
  induction first with
  | empty lower =>
      cases second with
      | empty => rfl
      | node left right => simp [DynamicOptimality.BST.toRaw, Auxiliary.map] at same
  | @node lower root upper left right ihl ihr =>
      cases second with
      | empty => simp [DynamicOptimality.BST.toRaw, Auxiliary.map] at same
      | @node _ other _ left' right' =>
          simp only [DynamicOptimality.BST.toRaw, Auxiliary.map, ChaCha.MTR.Tree.node.injEq] at same
          have count := congrArg size same.1
          simp only [map_size, DynamicOptimality.BST.toRaw_size] at count
          have firstCount := left.size_add_lower_eq_upper
          have secondCount := left'.size_add_lower_eq_upper
          have rootEq : other = root := by omega
          subst other
          exact congrArg₂ BST.node (ihl left' same.1) (ihr right' same.2.2)

theorem geometry_of_map_eq {aLower aUpper bLower bUpper : Nat}
    (first : BST aLower aUpper) (second : BST bLower bUpper) (a b : Nat → α)
    (same : Auxiliary.map a (DynamicOptimality.BST.toRaw first) = Auxiliary.map b (DynamicOptimality.BST.toRaw second)) :
    first.height = second.height ∧ leftBoundaryDepth first = leftBoundaryDepth second ∧
      rightBoundaryDepth first = rightBoundaryDepth second ∧
      ∀ slack, HasBoundedMinorRibs first slack ↔ HasBoundedMinorRibs second slack := by
  induction first generalizing bLower bUpper with
  | empty lower =>
      cases second with
      | empty => exact ⟨rfl, rfl, rfl, fun _ => Iff.rfl⟩
      | node left right => simp [DynamicOptimality.BST.toRaw, Auxiliary.map] at same
  | node left right ihl ihr =>
      cases second with
      | empty => simp [DynamicOptimality.BST.toRaw, Auxiliary.map] at same
      | node left' right' =>
          simp only [DynamicOptimality.BST.toRaw, Auxiliary.map, ChaCha.MTR.Tree.node.injEq] at same
          obtain ⟨lh, ll, lr, li⟩ := ihl left' same.1
          obtain ⟨rh, rl, rr, ri⟩ := ihr right' same.2.2
          simp [BST.height, leftBoundaryDepth, rightBoundaryDepth, HasBoundedMinorRibs, lh, rh, ll, lr, rl, rr, li, ri]

/-- Any other physical tree with the same inorder word can use the existing
local alphabet. Its physical shape is retained exactly. -/
theorem exists_on_same_alphabet [Inhabited α] {n : Nat} (reference : BST 0 n)
    (alphabet : Nat → α) (physical : RawTree α)
    (same : inorder physical = inorder (Auxiliary.map alphabet (DynamicOptimality.BST.toRaw reference))) :
    ∃ indexed : BST 0 n, Auxiliary.map alphabet (DynamicOptimality.BST.toRaw indexed) = physical := by
  obtain ⟨count, indexed, interpretation, represented, cardinality⟩ := exists_encoding physical
  have sizeEq : count = n := by
    have length := congrArg List.length same
    simp only [ChaCha.MTR.Tree.length_inorder, map_size, DynamicOptimality.BST.toRaw_size,
      BST.size_eq_upper] at length
    omega
  clear cardinality
  subst count
  have maps : (List.range' 0 n).map interpretation = (List.range' 0 n).map alphabet := by
    have observed := congrArg inorder represented
    rw [map_inorder, indexed_inorder, BST.size_eq_upper, same, map_inorder, indexed_inorder, BST.size_eq_upper] at observed
    exact observed
  have agree : ∀ key, 0 ≤ key → key < n → interpretation key = alphabet key := by
    intro key lower upper
    exact List.map_inj_left.mp maps key (by simp [List.mem_range']; omega)
  exact ⟨indexed, (indexed_congr indexed agree).symm.trans represented⟩

end MultiSplay.Alphabet

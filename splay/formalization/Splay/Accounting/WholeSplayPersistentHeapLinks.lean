import Splay.Accounting.WholeSplayHeapLinks
import Splay.Accounting.WholeSplayTemporaryFocusedTranscript

namespace Splay.Accounting

open Splay.Lazy Splay.Lazy.Canonical Splay.Rank Splay.Tree.BST
open WholeSplayTemporarySpineGeometry WholeSplayTemporaryFocusedSpines

/-- The fixed base and hanging subtrees of a right spine retain all their
internal heap links while subsequent rotations extend the spine. -/
noncomputable def rightPersistentLinks {n key baseUpper upper : ℕ} {snapshot : Snapshot n}
    {base : BST (key + 1) baseUpper} {tree : BST (key + 1) upper}
    (spine : RightSpine snapshot base tree) : Finset (External n × External n) :=
  match spine with
  | .base bound => heapLinks snapshot base bound
  | .grow inner hanging bound _ => rightPersistentLinks inner ∪ heapLinks snapshot hanging bound

noncomputable def leftPersistentLinks {n key baseLower lower : ℕ} {snapshot : Snapshot n}
    {base : BST baseLower key} {tree : BST lower key}
    (spine : LeftSpine snapshot base tree) : Finset (External n × External n) :=
  match spine with
  | .base bound => heapLinks snapshot base bound
  | .grow inner hanging bound _ _ => leftPersistentLinks inner ∪ heapLinks snapshot hanging bound

theorem rightPersistentLinks_subset {n key baseUpper upper : ℕ} {snapshot : Snapshot n}
    {base : BST (key + 1) baseUpper} {tree : BST (key + 1) upper}
    (spine : RightSpine snapshot base tree) :
    rightPersistentLinks spine ⊆ heapLinks snapshot tree spine.upper_le_n := by
  induction spine with
  | base bound => exact Finset.Subset.rfl
  | grow inner hanging bound heavy ih =>
      intro link member
      rw [heapLinks_node]
      rcases Finset.mem_union.mp member with inherited | attached
      · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr (ih inherited))))
      · exact Finset.mem_union.mpr (Or.inr attached)

theorem leftPersistentLinks_subset {n key baseLower lower : ℕ} {snapshot : Snapshot n}
    {base : BST baseLower key} {tree : BST lower key}
    (spine : LeftSpine snapshot base tree) :
    leftPersistentLinks spine ⊆ heapLinks snapshot tree spine.upper_le_n := by
  induction spine with
  | base bound => exact Finset.Subset.rfl
  | grow inner hanging bound keyBound heavy ih =>
      intro link member
      rw [heapLinks_node]
      rcases Finset.mem_union.mp member with inherited | attached
      · exact Finset.mem_union.mpr (Or.inr (ih inherited))
      · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr attached)))

theorem rightPersistentLinks_mono {n key baseUpper firstUpper secondUpper : ℕ} {snapshot : Snapshot n}
    {base : BST (key + 1) baseUpper} {firstTree : BST (key + 1) firstUpper} {secondTree : BST (key + 1) secondUpper}
    {first : RightSpine snapshot base firstTree} {second : RightSpine snapshot base secondTree}
    (extension : WholeSplayTemporaryFocusedSpines.RightSpine.IsPrefix first second) :
    rightPersistentLinks first ⊆ rightPersistentLinks second := by
  induction extension with
  | refl => exact Finset.Subset.rfl
  | grow _ _ _ _ ih => exact Finset.Subset.trans ih Finset.subset_union_left

theorem leftPersistentLinks_mono {n key baseLower firstLower secondLower : ℕ} {snapshot : Snapshot n}
    {base : BST baseLower key} {firstTree : BST firstLower key} {secondTree : BST secondLower key}
    {first : LeftSpine snapshot base firstTree} {second : LeftSpine snapshot base secondTree}
    (extension : WholeSplayTemporaryFocusedSpines.LeftSpine.IsPrefix first second) :
    leftPersistentLinks first ⊆ leftPersistentLinks second := by
  induction extension with
  | refl => exact Finset.Subset.rfl
  | grow _ _ _ _ _ ih => exact Finset.Subset.trans ih Finset.subset_union_left

/-- Every spine root follows the same heavy path down to the fixed base owner. -/
theorem rightSpine_owner_eq_base {n key baseUpper upper : ℕ} {snapshot : Snapshot n}
    {base : BST (key + 1) baseUpper} {tree : BST (key + 1) upper}
    (spine : RightSpine snapshot base tree) :
    subtreeOwner snapshot tree spine.upper_le_n = subtreeOwner snapshot base spine.base_le_n := by
  induction spine with
  | base bound => rfl
  | @grow root upper inner innerSpine hanging bound heavy ih =>
      let node : AtNode n := ⟨key + 1, root, upper, inner, hanging, bound⟩
      change node.heavyBranch snapshot = .left at heavy
      change node.owner snapshot = _
      rw [node.owner_eq_branchMin_heavy snapshot, heavy]
      exact ih

theorem leftSpine_owner_eq_base {n key baseLower lower : ℕ} {snapshot : Snapshot n}
    {base : BST baseLower key} {tree : BST lower key}
    (spine : LeftSpine snapshot base tree) :
    subtreeOwner snapshot tree spine.upper_le_n = subtreeOwner snapshot base spine.base_le_n := by
  induction spine with
  | base bound => rfl
  | @grow lower root inner innerSpine hanging bound keyBound heavy ih =>
      let node : AtNode n := ⟨lower, root, key, hanging, inner, keyBound⟩
      change node.heavyBranch snapshot = .right at heavy
      change node.owner snapshot = _
      rw [node.owner_eq_branchMin_heavy snapshot, heavy]
      exact ih

/-- Any right-spine link not owned by its fixed boundary is inside the
unchanged base or one of its hanging subtrees. -/
theorem rightSpine_link_persistent_of_owner_ne {n key baseUpper upper : ℕ} {snapshot : Snapshot n}
    {base : BST (key + 1) baseUpper} {tree : BST (key + 1) upper}
    (spine : RightSpine snapshot base tree) {link : External n × External n}
    (member : link ∈ heapLinks snapshot tree spine.upper_le_n)
    (other : link.1 ≠ subtreeOwner snapshot base spine.base_le_n) :
    link ∈ rightPersistentLinks spine := by
  induction spine with
  | base bound => exact member
  | @grow root upper inner innerSpine hanging bound heavy ih =>
      rw [heapLinks_node] at member
      rcases Finset.mem_union.mp member with localOrInner | hangingMember
      · rcases Finset.mem_union.mp localOrInner with localMember | innerMember
        · obtain ⟨edge, edgeMember, equal⟩ := List.mem_map.mp (List.mem_toFinset.mp localMember)
          have edgeValid := mem_edgesAtNode_valid snapshot ⟨key + 1, root, upper, inner, hanging, bound⟩ 0 edgeMember
          have ownerEq := rightSpine_owner_eq_base (RightSpine.grow innerSpine hanging bound heavy)
          apply False.elim
          apply other
          exact (congrArg Prod.fst equal).symm.trans (edgeValid.2.1.trans ownerEq)
        · exact Finset.mem_union.mpr (Or.inl (ih innerMember other))
      · exact Finset.mem_union.mpr (Or.inr hangingMember)

theorem leftSpine_link_persistent_of_owner_ne {n key baseLower lower : ℕ} {snapshot : Snapshot n}
    {base : BST baseLower key} {tree : BST lower key}
    (spine : LeftSpine snapshot base tree) {link : External n × External n}
    (member : link ∈ heapLinks snapshot tree spine.upper_le_n)
    (other : link.1 ≠ subtreeOwner snapshot base spine.base_le_n) :
    link ∈ leftPersistentLinks spine := by
  induction spine with
  | base bound => exact member
  | @grow lower root inner innerSpine hanging bound keyBound heavy ih =>
      rw [heapLinks_node] at member
      rcases Finset.mem_union.mp member with localOrHanging | innerMember
      · rcases Finset.mem_union.mp localOrHanging with localMember | hangingMember
        · obtain ⟨edge, edgeMember, equal⟩ := List.mem_map.mp (List.mem_toFinset.mp localMember)
          have edgeValid := mem_edgesAtNode_valid snapshot ⟨lower, root, key, hanging, inner, keyBound⟩ 0 edgeMember
          have ownerEq := leftSpine_owner_eq_base (LeftSpine.grow innerSpine hanging bound keyBound heavy)
          apply False.elim
          apply other
          exact (congrArg Prod.fst equal).symm.trans (edgeValid.2.1.trans ownerEq)
        · exact Finset.mem_union.mpr (Or.inr hangingMember)
      · exact Finset.mem_union.mpr (Or.inl (ih innerMember other))

/-- All persistent links below the promoted key in a focused intermediate tree. -/
noncomputable def focusedPersistentLinks {n lower upper : ℕ} {snapshot : Snapshot n} {key : Fin n}
    {leftBoundary rightBoundary : External n} {base : SpineBase key leftBoundary rightBoundary}
    {tree : BST lower upper} (focused : FocusedSpines snapshot key leftBoundary rightBoundary base tree) :
    Finset (External n × External n) :=
  leftPersistentLinks focused.spinePair.leftSpine ∪ rightPersistentLinks focused.spinePair.rightSpine

theorem focusedPersistentLinks_subset {n lower upper : ℕ} {snapshot : Snapshot n} {key : Fin n}
    {leftBoundary rightBoundary : External n} {base : SpineBase key leftBoundary rightBoundary}
    {tree : BST lower upper} (focused : FocusedSpines snapshot key leftBoundary rightBoundary base tree)
    (upper_le_n : upper ≤ n) :
    focusedPersistentLinks focused ⊆ heapLinks snapshot tree upper_le_n := by
  induction focused with
  | atKey leftSpine rightSpine =>
      intro link member
      rw [heapLinks_node]
      rcases Finset.mem_union.mp member with left | right
      · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr (leftPersistentLinks_subset leftSpine left))))
      · exact Finset.mem_union.mpr (Or.inr (rightPersistentLinks_subset rightSpine right))
  | leftContext focused rightTree ih =>
      intro link member
      rw [heapLinks_node]
      exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr (ih _ member))))
  | rightContext leftTree focused ih =>
      intro link member
      rw [heapLinks_node]
      exact Finset.mem_union.mpr (Or.inr (ih _ member))

theorem focusedPersistentLinks_mono {n firstLower firstUpper secondLower secondUpper : ℕ}
    {snapshot : Snapshot n} {key : Fin n} {leftBoundary rightBoundary : External n}
    {base : SpineBase key leftBoundary rightBoundary}
    {firstTree : BST firstLower firstUpper} {secondTree : BST secondLower secondUpper}
    {first : FocusedSpines snapshot key leftBoundary rightBoundary base firstTree}
    {second : FocusedSpines snapshot key leftBoundary rightBoundary base secondTree}
    (extension : FocusedSpines.IsPrefix first second) :
    focusedPersistentLinks first ⊆ focusedPersistentLinks second :=
  Finset.union_subset_union (leftPersistentLinks_mono extension.left) (rightPersistentLinks_mono extension.right)

end Splay.Accounting

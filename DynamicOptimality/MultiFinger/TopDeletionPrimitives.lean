import DynamicOptimality.MultiFinger.TopMarks

/-! # Removing a top marker while retaining its original physical key

After the predecessor and successor markers have been exposed in the two
children, two ordinary rotations put the removed marker inside the merged
opaque gap. The original physical key is retained. This final regrouping
does not increase the top-skeleton potential.
-/

namespace DynamicOptimality.MultiFinger.Top

open ChaCha.MTR
open Pointer (MarkedTree)
open SearchRotation
open ChaCha.Paper20261030.SplayAuxiliary (potential rank rank_mono)

variable {α : Type*}

/-- The gaps adjacent to the removed marker become one physical subtree;
all other gap trees keep their identities and left-to-right order. The
defaults are unused because a marked tree always has a nonempty gap list. -/
def mergedRootHoles (key : α) (left right : List (RawTree α)) : List (RawTree α) :=
  left.dropLast ++ [.node (left.getLastD .empty) key (right.headD .empty)] ++ right.tail

theorem holes_nonempty (tree : MarkedTree α) : tree.holes ≠ [] := by
  intro empty
  have size := tree.holes_length
  rw [empty,List.length_nil] at size
  omega

@[simp] theorem mergedRootHoles_append_cons (key : α)
    (left right : List (RawTree α)) (innerLeft innerRight : RawTree α) :
    mergedRootHoles key (left++[innerLeft]) (innerRight::right) =
      left++[.node innerLeft key innerRight]++right := by
  simp [mergedRootHoles,List.getLastD_concat]

theorem remove_both_holes (left right : MarkedTree α) (innerLeft innerRight : RawTree α)
    (lo key hi : α) :
    (MarkedTree.node left lo (.node (.hole (.node innerLeft key innerRight)) hi right)).holes =
      mergedRootHoles key (MarkedTree.node left lo (.hole innerLeft)).holes
        (MarkedTree.node (.hole innerRight) hi right).holes := by
  simp [MarkedTree.holes,List.append_assoc]

theorem remove_with_left_holes (left : MarkedTree α) (inner last : RawTree α) (lo key : α) :
    (MarkedTree.node left lo (.hole (.node inner key last))).holes =
      mergedRootHoles key (MarkedTree.node left lo (.hole inner)).holes [last] := by
  simp [MarkedTree.holes]

theorem remove_with_right_holes (right : MarkedTree α) (first inner : RawTree α) (key hi : α) :
    (MarkedTree.node (.hole (.node first key inner)) hi right).holes =
      mergedRootHoles key [first] (MarkedTree.node (.hole inner) hi right).holes := by
  simpa only [MarkedTree.holes,List.nil_append,List.singleton_append] using
    (mergedRootHoles_append_cons key [] right.holes first inner).symm

theorem remove_only_holes (left right : RawTree α) (key : α) :
    (MarkedTree.hole (.node left key right)).holes = mergedRootHoles key [left] [right] := by
  simp [MarkedTree.holes,mergedRootHoles,List.getLastD_cons]

theorem remove_both (left right : MarkedTree α) (innerLeft innerRight : RawTree α)
    (lo key hi : α) :
    let before := MarkedTree.node (.node left lo (.hole innerLeft)) key
      (.node (.hole innerRight) hi right)
    let after := MarkedTree.node left lo (.node (.hole (.node innerLeft key innerRight)) hi right)
    Rotations before.erase after.erase 2 ∧
      after.skeleton.size+1 = before.skeleton.size ∧
      potential after.skeleton ≤ potential before.skeleton := by
  dsimp only
  refine ⟨?_,?_,?_⟩
  · exact .step (.rootRight _ _ _ _ _) (.singleton (.rightContext _ _ (.rootLeft _ _ _ _ _)))
  · simp only [MarkedTree.skeleton,Tree.size]
    omega
  · have smaller := rank_mono
      (a := ChaCha.MTR.Tree.node left.skeleton lo (.node .empty hi right.skeleton))
      (b := ChaCha.MTR.Tree.node (.node left.skeleton lo .empty) key (.node .empty hi right.skeleton))
      (by simp only [Tree.size]; omega)
    simp only [MarkedTree.skeleton,potential]
    omega

theorem remove_with_left (left : MarkedTree α) (inner last : RawTree α) (lo key : α) :
    let before := MarkedTree.node (.node left lo (.hole inner)) key (.hole last)
    let after := MarkedTree.node left lo (.hole (.node inner key last))
    Rotations before.erase after.erase 1 ∧
      after.skeleton.size+1 = before.skeleton.size ∧
      potential after.skeleton ≤ potential before.skeleton := by
  dsimp only
  refine ⟨.singleton (.rootRight _ _ _ _ _),?_,?_⟩
  · simp only [MarkedTree.skeleton,Tree.size]
  · have smaller := rank_mono
      (a := ChaCha.MTR.Tree.node left.skeleton lo .empty)
      (b := ChaCha.MTR.Tree.node (.node left.skeleton lo .empty) key .empty)
      (by simp only [Tree.size]; omega)
    simp only [MarkedTree.skeleton,potential]
    omega

theorem remove_with_right (right : MarkedTree α) (first inner : RawTree α) (key hi : α) :
    let before := MarkedTree.node (.hole first) key (.node (.hole inner) hi right)
    let after := MarkedTree.node (.hole (.node first key inner)) hi right
    Rotations before.erase after.erase 1 ∧
      after.skeleton.size+1 = before.skeleton.size ∧
      potential after.skeleton ≤ potential before.skeleton := by
  dsimp only
  refine ⟨.singleton (.rootLeft _ _ _ _ _),?_,?_⟩
  · simp only [MarkedTree.skeleton,Tree.size]
    omega
  · have smaller := rank_mono
      (a := ChaCha.MTR.Tree.node .empty hi right.skeleton)
      (b := ChaCha.MTR.Tree.node .empty key (.node .empty hi right.skeleton))
      (by simp only [Tree.size]; omega)
    simp only [MarkedTree.skeleton,potential]
    omega

theorem remove_only (left right : RawTree α) (key : α) :
    let before := MarkedTree.node (.hole left) key (.hole right)
    let after := MarkedTree.hole (.node left key right)
    Rotations before.erase after.erase 0 ∧
      after.skeleton.size+1 = before.skeleton.size ∧
      potential after.skeleton ≤ potential before.skeleton := by
  exact ⟨.refl _,rfl,Nat.zero_le _⟩

end DynamicOptimality.MultiFinger.Top

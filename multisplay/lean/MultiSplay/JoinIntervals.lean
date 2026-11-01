import MultiSplay.HeapEmbedding

/-!
# Retained lazy intervals at a common root join

The old assigned lists are joined with the two former roots. The new pivot is
the only unassigned root. Existing intervals keep their element order, owner,
mode, pass count, and attained gap; the other component is a passive frame.
-/

namespace MultiSplay.JoinIntervals

open Splay.Tree (BST)
open Splay.Rank (Snapshot External)
open Splay.Lazy (HeapView Element Side Block)
open Splay.Lazy.Canonical
open RankEmbedding (external)

abbrev leftEmbedding (l r : Nat) : External l → External (0 + l + 1 + r) := external 0 (by omega)
abbrev rightEmbedding (l r : Nat) : External r → External (0 + l + 1 + r) := external (0 + l + 1) (by omega)

theorem left_ne_pivot (l r : Nat) (x : External l) : leftEmbedding l r x ≠ JoinRanks.pivot l r := by
  intro same
  have h := congrArg Fin.val same
  have bound := x.isLt
  dsimp [leftEmbedding, external, JoinRanks.pivot] at h
  omega

theorem right_ne_pivot (l r : Nat) (x : External r) : rightEmbedding l r x ≠ JoinRanks.pivot l r := by
  intro same
  have h := congrArg Fin.val same
  dsimp [rightEmbedding, external, JoinRanks.pivot] at h
  omega

theorem disjoint (l r : Nat) (x : External l) (y : External r) : leftEmbedding l r x ≠ rightEmbedding l r y := by
  intro same
  have h := congrArg Fin.val same
  have bound := x.isLt
  dsimp [leftEmbedding, rightEmbedding, external] at h
  omega

noncomputable def view {l r : Nat} (left : BST 0 l) (right : BST 0 r)
    (splayLeft : BST 0 l) (splayRight : BST 0 r) : HeapView (0 + l + 1 + r) :=
  canonicalHeapView (Snapshot.ofTree (JoinRanks.tree left right)) (JoinRanks.tree splayLeft splayRight)

noncomputable def assigned {l r : Nat} (left : BST 0 l) (right : BST 0 r)
    (splayLeft : BST 0 l) (splayRight : BST 0 r) (a : List (External l)) (b : List (External r)) :
    List (External (0 + l + 1 + r)) :=
  [leftEmbedding l r (canonicalRoot (Snapshot.ofTree left) splayLeft),
   rightEmbedding l r (canonicalRoot (Snapshot.ofTree right) splayRight)] ++
    a.map (leftEmbedding l r) ++ b.map (rightEmbedding l r)

theorem root_eq {l r : Nat} (left : BST 0 l) (right : BST 0 r)
    (splayLeft : BST 0 l) (splayRight : BST 0 r) :
    (view left right splayLeft splayRight).root = JoinRanks.pivot l r :=
  JoinRanks.root_owner left right splayLeft splayRight

theorem left_root_side {l r : Nat} (left : BST 0 l) (right : BST 0 r)
    (splayLeft : BST 0 l) (splayRight : BST 0 r) :
    (view left right splayLeft splayRight).side
      (leftEmbedding l r (canonicalRoot (Snapshot.ofTree left) splayLeft)) = .left := by
  have parent := JoinHeap.left_root_parent left right splayLeft splayRight
  have order := (view left right splayLeft splayRight).side_order parent
  cases sideEq : (view left right splayLeft splayRight).side
      (leftEmbedding l r (canonicalRoot (Snapshot.ofTree left) splayLeft)) with
  | left => rfl
  | right =>
      rw [sideEq] at order
      have bound := (canonicalRoot (Snapshot.ofTree left) splayLeft).isLt
      dsimp [leftEmbedding, external, JoinRanks.pivot] at order
      omega

theorem right_root_side {l r : Nat} (left : BST 0 l) (right : BST 0 r)
    (splayLeft : BST 0 l) (splayRight : BST 0 r) :
    (view left right splayLeft splayRight).side
      (rightEmbedding l r (canonicalRoot (Snapshot.ofTree right) splayRight)) = .right := by
  have parent := JoinHeap.right_root_parent left right splayLeft splayRight
  have order := (view left right splayLeft splayRight).side_order parent
  cases sideEq : (view left right splayLeft splayRight).side
      (rightEmbedding l r (canonicalRoot (Snapshot.ofTree right) splayRight)) with
  | left =>
      rw [sideEq] at order
      dsimp [rightEmbedding, external, JoinRanks.pivot] at order
      omega
  | right => rfl

/-- The new universe has exactly the two old images and the new pivot. -/
theorem cases_element (l r : Nat) (element : External (0 + l + 1 + r)) :
    (∃ old, leftEmbedding l r old = element) ∨ element = JoinRanks.pivot l r ∨
      (∃ old, rightEmbedding l r old = element) := by
  by_cases left : element.val < 2 * l + 1
  · exact Or.inl ⟨⟨element.val, left⟩, by apply Fin.ext; simp [leftEmbedding, external]⟩
  · by_cases middle : element.val = 2 * l + 1
    · exact Or.inr (Or.inl (by apply Fin.ext; simpa [JoinRanks.pivot] using middle))
    · have bound := element.isLt
      refine Or.inr (Or.inr ⟨⟨element.val - (2 * l + 2), by omega⟩, ?_⟩)
      apply Fin.ext
      dsimp [rightEmbedding, external]
      omega

theorem left_links {l r : Nat} (left : BST 0 l) (right : BST 0 r)
    (splayLeft : BST 0 l) (splayRight : BST 0 r) {element : External l}
    (notRoot : element ≠ canonicalRoot (Snapshot.ofTree left) splayLeft) :
    (view left right splayLeft splayRight).parent (leftEmbedding l r element) =
        ((canonicalHeapView (Snapshot.ofTree left) splayLeft).parent element).map (leftEmbedding l r) ∧
      (view left right splayLeft splayRight).side (leftEmbedding l r element) =
        (canonicalHeapView (Snapshot.ofTree left) splayLeft).side element := by
  obtain ⟨edge, found, _, _⟩ := exists_incomingEdge?_eq_some_of_ne_root (Snapshot.ofTree left) splayLeft notRoot
  have after := JoinHeap.left_incoming left right splayLeft splayRight found
  simp only [view, canonicalHeapView, canonicalParent, canonicalSide, found, after, leftEmbedding,
    Option.map_some, RankEmbedding.edge]
  trivial

theorem right_links {l r : Nat} (left : BST 0 l) (right : BST 0 r)
    (splayLeft : BST 0 l) (splayRight : BST 0 r) {element : External r}
    (notRoot : element ≠ canonicalRoot (Snapshot.ofTree right) splayRight) :
    (view left right splayLeft splayRight).parent (rightEmbedding l r element) =
        ((canonicalHeapView (Snapshot.ofTree right) splayRight).parent element).map (rightEmbedding l r) ∧
      (view left right splayLeft splayRight).side (rightEmbedding l r element) =
        (canonicalHeapView (Snapshot.ofTree right) splayRight).side element := by
  obtain ⟨edge, found, _, _⟩ := exists_incomingEdge?_eq_some_of_ne_root (Snapshot.ofTree right) splayRight notRoot
  have after := JoinHeap.right_incoming left right splayLeft splayRight found
  simp only [view, canonicalHeapView, canonicalParent, canonicalSide, found, after, rightEmbedding,
    Option.map_some, RankEmbedding.edge]
  trivial

theorem left_children {l r : Nat} (left : BST 0 l) (right : BST 0 r)
    (splayLeft : BST 0 l) (splayRight : BST 0 r) (a : List (External l)) (b : List (External r))
    (aRoot : canonicalRoot (Snapshot.ofTree left) splayLeft ∉ a)
    (bRoot : canonicalRoot (Snapshot.ofTree right) splayRight ∉ b)
    (owner : External l) (side : Side) :
    (view left right splayLeft splayRight).attachedTopDown (assigned left right splayLeft splayRight a b)
      (leftEmbedding l r owner) side =
      ((canonicalHeapView (Snapshot.ofTree left) splayLeft).attachedTopDown a owner side).map (leftEmbedding l r) := by
  apply HeapEmbedding.attachedTopDown_framed (leftEmbedding l r) (RankEmbedding.external_injective _ _)
    (fun x y => RankEmbedding.external_lt _ _ x y)
    (canonicalHeapView (Snapshot.ofTree left) splayLeft) (view left right splayLeft splayRight)
    a (assigned left right splayLeft splayRight a b)
    ([leftEmbedding l r (canonicalRoot (Snapshot.ofTree left) splayLeft),
      rightEmbedding l r (canonicalRoot (Snapshot.ofTree right) splayRight)] ++ b.map (rightEmbedding l r)) owner side
  · intro element
    simp only [assigned, List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
    tauto
  · intro element member
    exact left_links left right splayLeft splayRight (fun same => aRoot (same ▸ member))
  · intro element member parent
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with (rfl | rfl) | other
    · have hp := JoinHeap.left_root_parent left right splayLeft splayRight
      have same : JoinRanks.pivot l r = leftEmbedding l r owner := Option.some.inj (hp.symm.trans parent)
      exact left_ne_pivot l r owner same.symm
    · have hp := JoinHeap.right_root_parent left right splayLeft splayRight
      have same : JoinRanks.pivot l r = leftEmbedding l r owner := Option.some.inj (hp.symm.trans parent)
      exact left_ne_pivot l r owner same.symm
    · obtain ⟨original, originalMem, rfl⟩ := List.mem_map.mp other
      have notRoot : original ≠ canonicalRoot (Snapshot.ofTree right) splayRight := fun same => bRoot (same ▸ originalMem)
      obtain ⟨oldOwner, oldParent⟩ := exists_canonicalParent_eq_some_of_ne_root (Snapshot.ofTree right) splayRight notRoot
      have hp := JoinHeap.right_parent left right splayLeft splayRight oldParent
      have same : rightEmbedding l r oldOwner = leftEmbedding l r owner := Option.some.inj (hp.symm.trans parent)
      exact disjoint l r owner oldOwner same.symm

theorem right_children {l r : Nat} (left : BST 0 l) (right : BST 0 r)
    (splayLeft : BST 0 l) (splayRight : BST 0 r) (a : List (External l)) (b : List (External r))
    (aRoot : canonicalRoot (Snapshot.ofTree left) splayLeft ∉ a)
    (bRoot : canonicalRoot (Snapshot.ofTree right) splayRight ∉ b)
    (owner : External r) (side : Side) :
    (view left right splayLeft splayRight).attachedTopDown (assigned left right splayLeft splayRight a b)
      (rightEmbedding l r owner) side =
      ((canonicalHeapView (Snapshot.ofTree right) splayRight).attachedTopDown b owner side).map (rightEmbedding l r) := by
  apply HeapEmbedding.attachedTopDown_framed (rightEmbedding l r) (RankEmbedding.external_injective _ _)
    (fun x y => RankEmbedding.external_lt _ _ x y)
    (canonicalHeapView (Snapshot.ofTree right) splayRight) (view left right splayLeft splayRight)
    b (assigned left right splayLeft splayRight a b)
    ([leftEmbedding l r (canonicalRoot (Snapshot.ofTree left) splayLeft),
      rightEmbedding l r (canonicalRoot (Snapshot.ofTree right) splayRight)] ++ a.map (leftEmbedding l r)) owner side
  · intro element
    simp only [assigned, List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
    tauto
  · intro element member
    exact right_links left right splayLeft splayRight (fun same => bRoot (same ▸ member))
  · intro element member parent
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with (rfl | rfl) | other
    · have hp := JoinHeap.left_root_parent left right splayLeft splayRight
      have same : JoinRanks.pivot l r = rightEmbedding l r owner := Option.some.inj (hp.symm.trans parent)
      exact right_ne_pivot l r owner same.symm
    · have hp := JoinHeap.right_root_parent left right splayLeft splayRight
      have same : JoinRanks.pivot l r = rightEmbedding l r owner := Option.some.inj (hp.symm.trans parent)
      exact right_ne_pivot l r owner same.symm
    · obtain ⟨original, originalMem, rfl⟩ := List.mem_map.mp other
      have notRoot : original ≠ canonicalRoot (Snapshot.ofTree left) splayLeft := fun same => aRoot (same ▸ originalMem)
      obtain ⟨oldOwner, oldParent⟩ := exists_canonicalParent_eq_some_of_ne_root (Snapshot.ofTree left) splayLeft notRoot
      have hp := JoinHeap.left_parent left right splayLeft splayRight oldParent
      have same : leftEmbedding l r oldOwner = rightEmbedding l r owner := Option.some.inj (hp.symm.trans parent)
      exact disjoint l r oldOwner owner same

theorem left_structurallyValid {l r : Nat} (left : BST 0 l) (right : BST 0 r)
    (splayLeft : BST 0 l) (splayRight : BST 0 r) (a : List (External l)) (b : List (External r))
    (aRoot : canonicalRoot (Snapshot.ofTree left) splayLeft ∉ a)
    (bRoot : canonicalRoot (Snapshot.ofTree right) splayRight ∉ b)
    (source : Block l)
    (valid : source.StructurallyValid (canonicalHeapView (Snapshot.ofTree left) splayLeft) a) :
    (BlockEmbedding.block (leftEmbedding l r) source).StructurallyValid
      (view left right splayLeft splayRight) (assigned left right splayLeft splayRight a b) := by
  apply HeapEmbedding.structurallyValid _ _ _ a _ source valid
    (left_children left right splayLeft splayRight a b aRoot bRoot source.owner source.side)
  intro element member
  exact JoinHeap.left_rawGap left right splayLeft splayRight (BlockEmbedding.member_ne_root _ source a valid member)

theorem right_structurallyValid {l r : Nat} (left : BST 0 l) (right : BST 0 r)
    (splayLeft : BST 0 l) (splayRight : BST 0 r) (a : List (External l)) (b : List (External r))
    (aRoot : canonicalRoot (Snapshot.ofTree left) splayLeft ∉ a)
    (bRoot : canonicalRoot (Snapshot.ofTree right) splayRight ∉ b)
    (source : Block r)
    (valid : source.StructurallyValid (canonicalHeapView (Snapshot.ofTree right) splayRight) b) :
    (BlockEmbedding.block (rightEmbedding l r) source).StructurallyValid
      (view left right splayLeft splayRight) (assigned left right splayLeft splayRight a b) := by
  apply HeapEmbedding.structurallyValid _ _ _ b _ source valid
    (right_children left right splayLeft splayRight a b aRoot bRoot source.owner source.side)
  intro element member
  exact JoinHeap.right_rawGap left right splayLeft splayRight (BlockEmbedding.member_ne_root _ source b valid member)

end MultiSplay.JoinIntervals

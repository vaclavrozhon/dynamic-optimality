import MultiSplay.JoinRootGeometry
import MultiSplay.RichRestriction

/-! # History-independent component embeddings at a common root -/

namespace MultiSplay.JoinComponentGeometry

open Splay.Tree (BST)
open Splay.Rank (Snapshot External)
open Splay.Lazy (HeapView Side)
open Splay.Lazy.Canonical
open JoinIntervals (leftEmbedding rightEmbedding)

variable {n l r : Nat}

noncomputable def nonroots (view : HeapView n) : List (External n) :=
  (List.finRange (2*n+1)).filter (fun x => decide (x ≠ view.root))

@[simp] theorem mem_nonroots (view : HeapView n) (x : External n) : x ∈ nonroots view ↔ x ≠ view.root := by
  simp [nonroots]

theorem attached_nonroots (view : HeapView n) (owner : External n) (side : Side) :
    view.attachedTopDown (nonroots view) owner side = view.topDown owner side := by
  apply List.filter_eq_self.mpr
  intro x member
  apply decide_eq_true
  apply (mem_nonroots view x).mpr
  intro eq
  have parent := view.mem_topDown_parent member
  rw [eq, view.root_parent] at parent
  cases parent

theorem assigned_nonroots (left : BST 0 l) (right : BST 0 r) (sl : BST 0 l) (sr : BST 0 r)
    (x : External (0+l+1+r)) (nonroot : x ≠ JoinRanks.pivot l r) :
    x ∈ JoinIntervals.assigned left right sl sr
      (nonroots (canonicalHeapView (Snapshot.ofTree left) sl)) (nonroots (canonicalHeapView (Snapshot.ofTree right) sr)) := by
  rcases JoinIntervals.cases_element l r x with ⟨old, rfl⟩ | rfl | ⟨old, rfl⟩
  · by_cases isRoot : old = canonicalRoot (Snapshot.ofTree left) sl
    · simp [JoinIntervals.assigned, isRoot]
    · have member : old ∈ nonroots (canonicalHeapView (Snapshot.ofTree left) sl) := (mem_nonroots _ _).mpr isRoot
      exact List.mem_append_left _ (List.mem_append_right _ (List.mem_map.mpr ⟨old, member, rfl⟩))
  · exact False.elim (nonroot rfl)
  · by_cases isRoot : old = canonicalRoot (Snapshot.ofTree right) sr
    · simp [JoinIntervals.assigned, isRoot]
    · have member : old ∈ nonroots (canonicalHeapView (Snapshot.ofTree right) sr) := (mem_nonroots _ _).mpr isRoot
      exact List.mem_append_right _ (List.mem_map.mpr ⟨old, member, rfl⟩)

theorem attached_join (left : BST 0 l) (right : BST 0 r) (sl : BST 0 l) (sr : BST 0 r)
    (owner : External (0+l+1+r)) (side : Side) :
    (JoinIntervals.view left right sl sr).attachedTopDown
      (JoinIntervals.assigned left right sl sr (nonroots (canonicalHeapView (Snapshot.ofTree left) sl))
        (nonroots (canonicalHeapView (Snapshot.ofTree right) sr))) owner side =
      (JoinIntervals.view left right sl sr).topDown owner side := by
  apply List.filter_eq_self.mpr
  intro x member
  apply decide_eq_true
  apply assigned_nonroots
  intro eq
  have parent := (JoinIntervals.view left right sl sr).mem_topDown_parent member
  rw [eq, ← JoinIntervals.root_eq left right sl sr, HeapView.root_parent] at parent
  cases parent

theorem left_topDown (left : BST 0 l) (right : BST 0 r) (sl : BST 0 l) (sr : BST 0 r)
    (owner : External l) (side : Side) :
    (JoinIntervals.view left right sl sr).topDown (leftEmbedding l r owner) side =
      ((canonicalHeapView (Snapshot.ofTree left) sl).topDown owner side).map (leftEmbedding l r) := by
  rw [← attached_join left right sl sr, JoinIntervals.left_children]
  · rw [attached_nonroots]
  · simp [canonicalHeapView]
  · simp [canonicalHeapView]

theorem right_topDown (left : BST 0 l) (right : BST 0 r) (sl : BST 0 l) (sr : BST 0 r)
    (owner : External r) (side : Side) :
    (JoinIntervals.view left right sl sr).topDown (rightEmbedding l r owner) side =
      ((canonicalHeapView (Snapshot.ofTree right) sr).topDown owner side).map (rightEmbedding l r) := by
  rw [← attached_join left right sl sr, JoinIntervals.right_children]
  · rw [attached_nonroots]
  · simp [canonicalHeapView]
  · simp [canonicalHeapView]

theorem priority_topDown (snapshot : Snapshot n) (tree : BST 0 n) (owner : External n) (side : Side) :
    (canonicalHeapView snapshot.withTruePriority tree).topDown owner side =
      (canonicalHeapView snapshot tree).topDown owner side := by
  have eq := JoinPriority.attached_eq snapshot tree (List.finRange (2*n+1)) owner side
  simpa [HeapView.attachedTopDown] using eq

noncomputable def left (left : BST 0 l) (right : BST 0 r) (sl : BST 0 l) (sr : BST 0 r) :
    RichRestriction.Embedding (canonicalHeapView (Snapshot.ofTree left).withTruePriority sl)
      (canonicalHeapView (Snapshot.ofTree (JoinRanks.tree left right)).withTruePriority (JoinRanks.tree sl sr)) where
  element := leftEmbedding l r
  injective := RankEmbedding.external_injective _ _
  children := by
    intro owner side
    rw [priority_topDown, priority_topDown]
    exact left_topDown left right sl sr owner side
  gap := fun _ notRoot => JoinPriority.left_rawGap left right sl sr notRoot

noncomputable def right (left : BST 0 l) (right : BST 0 r) (sl : BST 0 l) (sr : BST 0 r) :
    RichRestriction.Embedding (canonicalHeapView (Snapshot.ofTree right).withTruePriority sr)
      (canonicalHeapView (Snapshot.ofTree (JoinRanks.tree left right)).withTruePriority (JoinRanks.tree sl sr)) where
  element := rightEmbedding l r
  injective := RankEmbedding.external_injective _ _
  children := by
    intro owner side
    rw [priority_topDown, priority_topDown]
    exact right_topDown left right sl sr owner side
  gap := fun _ notRoot => JoinPriority.right_rawGap left right sl sr notRoot

end MultiSplay.JoinComponentGeometry

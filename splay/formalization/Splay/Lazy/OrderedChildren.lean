import Mathlib.Data.List.Pairwise
import Splay.Lazy.Model

namespace Splay.Lazy

/--
All children of `owner` on `childSide`, in the order used by `HeapView`:
increasing element order on the left and decreasing element order on the right.
-/
def orderedChildren {n : ℕ}
    (parent : Element n → Option (Element n))
    (side : Element n → Side) (owner : Element n)
    (childSide : Side) : List (Element n) :=
  let children :=
    (List.finRange (2 * n + 1)).filter fun element =>
      decide (parent element = some owner ∧ side element = childSide)
  match childSide with
  | .left => children
  | .right => children.reverse

@[simp]
theorem mem_orderedChildren_iff {n : ℕ}
    (parent : Element n → Option (Element n))
    (side : Element n → Side) {owner element : Element n}
    {childSide : Side} :
    element ∈ orderedChildren parent side owner childSide ↔
      parent element = some owner ∧ side element = childSide := by
  cases childSide <;> simp [orderedChildren]

theorem orderedChildren_nodup {n : ℕ}
    (parent : Element n → Option (Element n))
    (side : Element n → Side) (owner : Element n)
    (childSide : Side) :
    (orderedChildren parent side owner childSide).Nodup := by
  cases childSide
  · exact (List.nodup_finRange (2 * n + 1)).filter _
  · exact List.nodup_reverse.mpr
      ((List.nodup_finRange (2 * n + 1)).filter _)

theorem orderedChildren_pairwise {n : ℕ}
    (parent : Element n → Option (Element n))
    (side : Element n → Side) (owner : Element n)
    (childSide : Side) :
    match childSide with
    | .left =>
        (orderedChildren parent side owner .left).Pairwise
          (fun earlier later => earlier.val < later.val)
    | .right =>
        (orderedChildren parent side owner .right).Pairwise
          (fun earlier later => later.val < earlier.val) := by
  cases childSide
  · exact (List.pairwise_lt_finRange (2 * n + 1)).filter _
  · exact ((List.pairwise_lt_finRange (2 * n + 1)).filter _).reverse

/-- The two ordering facts in exactly the shape required by `HeapView`. -/
theorem orderedChildren_ordered {n : ℕ}
    (parent : Element n → Option (Element n))
    (side : Element n → Side) (owner : Element n) :
    (orderedChildren parent side owner .left).Pairwise
        (fun earlier later => earlier.val < later.val) ∧
      (orderedChildren parent side owner .right).Pairwise
        (fun earlier later => later.val < earlier.val) :=
  ⟨orderedChildren_pairwise parent side owner .left,
    orderedChildren_pairwise parent side owner .right⟩

namespace HeapView

/-- Data of one requested heap-child reparenting. -/
structure ReparentInstruction (n : ℕ) where
  winner : Element n
  loser : Element n
  side : Side

/-- Reparent one non-root heap child while retaining all ranks.

The new top-down lists are reconstructed from the resulting parent/side
functions, so their duplicate-freeness, ordering, and membership laws are
automatic.  Taking comparison rank itself as the structural level is sound
because both the old view and the new edge are heap ordered. -/
noncomputable def reparentOne {n : ℕ} (view : HeapView n)
    (winner loser : Element n) (newSide : Side)
    (ordered : view.HeapOrdered)
    (loserNotRoot : loser ≠ view.root)
    (rankLt : view.rank winner < view.rank loser)
    (newSideOrder :
      match newSide with
      | .left => loser.val < winner.val
      | .right => winner.val < loser.val) : HeapView n where
  rank := view.rank
  root := view.root
  parent := fun element =>
    if element = loser then some winner else view.parent element
  side := fun element =>
    if element = loser then newSide else view.side element
  topDown := orderedChildren
    (fun element =>
      if element = loser then some winner else view.parent element)
    (fun element =>
      if element = loser then newSide else view.side element)
  level := view.rank
  root_parent := by
    simp [loserNotRoot.symm, view.root_parent]
  parent_eq_none := by
    intro element parentNone
    by_cases selected : element = loser
    · simp [selected] at parentNone
    · simp [selected] at parentNone
      exact view.parent_eq_none element parentNone
  parent_level_lt := by
    intro element owner parentEq
    by_cases selected : element = loser
    · subst element
      simp only [↓reduceIte, Option.some.injEq] at parentEq
      subst owner
      exact rankLt
    · simp only [selected, ↓reduceIte] at parentEq
      exact ordered parentEq
  side_order := by
    intro element owner parentEq
    by_cases selected : element = loser
    · subst element
      simp only [↓reduceIte, Option.some.injEq] at parentEq
      subst owner
      simp only [if_pos rfl]
      exact newSideOrder
    · simp only [selected, ↓reduceIte] at parentEq
      simp only [if_neg selected]
      exact view.side_order parentEq
  topDown_nodup := orderedChildren_nodup _ _
  topDown_ordered := orderedChildren_ordered _ _
  mem_topDown_iff := by
    intro owner childSide element
    exact mem_orderedChildren_iff _ _

@[simp]
theorem reparentOne_rank {n : ℕ} (view : HeapView n)
    (winner loser : Element n) (newSide : Side)
    (ordered : view.HeapOrdered) (loserNotRoot : loser ≠ view.root)
    (rankLt : view.rank winner < view.rank loser)
    (newSideOrder) :
    (view.reparentOne winner loser newSide ordered loserNotRoot rankLt
      newSideOrder).rank = view.rank := rfl

@[simp]
theorem reparentOne_root {n : ℕ} (view : HeapView n)
    (winner loser : Element n) (newSide : Side)
    (ordered : view.HeapOrdered) (loserNotRoot : loser ≠ view.root)
    (rankLt : view.rank winner < view.rank loser)
    (newSideOrder) :
    (view.reparentOne winner loser newSide ordered loserNotRoot rankLt
      newSideOrder).root = view.root := rfl

@[simp]
theorem reparentOne_parent {n : ℕ} (view : HeapView n)
    (winner loser element : Element n) (newSide : Side)
    (ordered : view.HeapOrdered) (loserNotRoot : loser ≠ view.root)
    (rankLt : view.rank winner < view.rank loser)
    (newSideOrder) :
    (view.reparentOne winner loser newSide ordered loserNotRoot rankLt
      newSideOrder).parent element =
        if element = loser then some winner else view.parent element := rfl

@[simp]
theorem reparentOne_side {n : ℕ} (view : HeapView n)
    (winner loser element : Element n) (newSide : Side)
    (ordered : view.HeapOrdered) (loserNotRoot : loser ≠ view.root)
    (rankLt : view.rank winner < view.rank loser)
    (newSideOrder) :
    (view.reparentOne winner loser newSide ordered loserNotRoot rankLt
      newSideOrder).side element =
        if element = loser then newSide else view.side element := rfl

/-- Reparenting preserves heap order when the new edge has increasing rank. -/
theorem reparentOne_heapOrdered {n : ℕ} (view : HeapView n)
    (winner loser : Element n) (newSide : Side)
    (ordered : view.HeapOrdered) (loserNotRoot : loser ≠ view.root)
    (rankLt : view.rank winner < view.rank loser)
    (newSideOrder) :
    (view.reparentOne winner loser newSide ordered loserNotRoot rankLt
      newSideOrder).HeapOrdered := by
  intro element owner parentEq
  by_cases selected : element = loser
  · subst element
    simp only [reparentOne_parent, ↓reduceIte, Option.some.injEq] at parentEq
    subst owner
    exact rankLt
  · simp only [reparentOne_parent, selected, ↓reduceIte] at parentEq
    exact ordered parentEq

/-- Apply a finite list of rank-increasing reparentings.  The proof arguments
are stated against the view at the current recursive stage; since every step
preserves ranks and the root definitionally, the tail obligations transport
without any semantic work. -/
noncomputable def reparentMany {n : ℕ} :
    (view : HeapView n) →
    (instructions : List (ReparentInstruction n)) →
    view.HeapOrdered →
    (∀ instruction ∈ instructions,
      instruction.loser ≠ view.root) →
    (∀ instruction ∈ instructions,
      view.rank instruction.winner < view.rank instruction.loser) →
    (∀ instruction ∈ instructions,
      match instruction.side with
      | .left => instruction.loser.val < instruction.winner.val
      | .right => instruction.winner.val < instruction.loser.val) →
    HeapView n
  | view, [], _, _, _, _ => view
  | view, instruction :: instructions, ordered, loserNotRoot, rankLt,
      sideOrder =>
      let next := view.reparentOne instruction.winner instruction.loser
        instruction.side ordered
        (loserNotRoot instruction (by simp))
        (rankLt instruction (by simp))
        (sideOrder instruction (by simp))
      reparentMany next instructions
        (view.reparentOne_heapOrdered instruction.winner instruction.loser
          instruction.side ordered
          (loserNotRoot instruction (by simp))
          (rankLt instruction (by simp))
          (sideOrder instruction (by simp)))
        (by
          intro later laterMember
          exact loserNotRoot later (by simp [laterMember]))
        (by
          intro later laterMember
          exact rankLt later (by simp [laterMember]))
        (by
          intro later laterMember
          exact sideOrder later (by simp [laterMember]))

@[simp]
theorem reparentMany_nil {n : ℕ} (view : HeapView n)
    (ordered : view.HeapOrdered) (loserNotRoot) (rankLt) (sideOrder) :
    reparentMany view [] ordered loserNotRoot rankLt sideOrder = view := rfl

@[simp]
theorem reparentMany_rank {n : ℕ} (view : HeapView n)
    (instructions : List (ReparentInstruction n))
    (ordered : view.HeapOrdered) (loserNotRoot) (rankLt) (sideOrder) :
    (reparentMany view instructions ordered loserNotRoot rankLt
      sideOrder).rank = view.rank := by
  induction instructions generalizing view with
  | nil => rfl
  | cons instruction instructions ih =>
      let headNotRoot := loserNotRoot instruction (by simp)
      let headRankLt := rankLt instruction (by simp)
      let headSideOrder := sideOrder instruction (by simp)
      let next := view.reparentOne instruction.winner instruction.loser
        instruction.side ordered headNotRoot headRankLt headSideOrder
      have nextOrdered : next.HeapOrdered :=
        view.reparentOne_heapOrdered instruction.winner instruction.loser
          instruction.side ordered headNotRoot headRankLt headSideOrder
      have tailNotRoot : ∀ later ∈ instructions,
          later.loser ≠ next.root := by
        intro later laterMember
        exact loserNotRoot later (by simp [laterMember])
      have tailRankLt : ∀ later ∈ instructions,
          next.rank later.winner < next.rank later.loser := by
        intro later laterMember
        exact rankLt later (by simp [laterMember])
      have tailSideOrder : ∀ later ∈ instructions,
          match later.side with
          | .left => later.loser.val < later.winner.val
          | .right => later.winner.val < later.loser.val := by
        intro later laterMember
        exact sideOrder later (by simp [laterMember])
      exact ih next nextOrdered tailNotRoot tailRankLt tailSideOrder

@[simp]
theorem reparentMany_root {n : ℕ} (view : HeapView n)
    (instructions : List (ReparentInstruction n))
    (ordered : view.HeapOrdered) (loserNotRoot) (rankLt) (sideOrder) :
    (reparentMany view instructions ordered loserNotRoot rankLt
      sideOrder).root = view.root := by
  induction instructions generalizing view with
  | nil => rfl
  | cons instruction instructions ih =>
      let headNotRoot := loserNotRoot instruction (by simp)
      let headRankLt := rankLt instruction (by simp)
      let headSideOrder := sideOrder instruction (by simp)
      let next := view.reparentOne instruction.winner instruction.loser
        instruction.side ordered headNotRoot headRankLt headSideOrder
      have nextOrdered : next.HeapOrdered :=
        view.reparentOne_heapOrdered instruction.winner instruction.loser
          instruction.side ordered headNotRoot headRankLt headSideOrder
      have tailNotRoot : ∀ later ∈ instructions,
          later.loser ≠ next.root := by
        intro later laterMember
        exact loserNotRoot later (by simp [laterMember])
      have tailRankLt : ∀ later ∈ instructions,
          next.rank later.winner < next.rank later.loser := by
        intro later laterMember
        exact rankLt later (by simp [laterMember])
      have tailSideOrder : ∀ later ∈ instructions,
          match later.side with
          | .left => later.loser.val < later.winner.val
          | .right => later.winner.val < later.loser.val := by
        intro later laterMember
        exact sideOrder later (by simp [laterMember])
      simpa [reparentMany, next, headNotRoot, headRankLt,
        headSideOrder] using
        ih next nextOrdered tailNotRoot tailRankLt tailSideOrder

/-- Every finite batch constructed by `reparentMany` remains heap ordered. -/
theorem reparentMany_heapOrdered {n : ℕ} (view : HeapView n)
    (instructions : List (ReparentInstruction n))
    (ordered : view.HeapOrdered) (loserNotRoot) (rankLt) (sideOrder) :
    (reparentMany view instructions ordered loserNotRoot rankLt
      sideOrder).HeapOrdered := by
  induction instructions generalizing view with
  | nil => exact ordered
  | cons instruction instructions ih =>
      let headNotRoot := loserNotRoot instruction (by simp)
      let headRankLt := rankLt instruction (by simp)
      let headSideOrder := sideOrder instruction (by simp)
      let next := view.reparentOne instruction.winner instruction.loser
        instruction.side ordered headNotRoot headRankLt headSideOrder
      have nextOrdered : next.HeapOrdered :=
        view.reparentOne_heapOrdered instruction.winner instruction.loser
          instruction.side ordered headNotRoot headRankLt headSideOrder
      have tailNotRoot : ∀ later ∈ instructions,
          later.loser ≠ next.root := by
        intro later laterMember
        exact loserNotRoot later (by simp [laterMember])
      have tailRankLt : ∀ later ∈ instructions,
          next.rank later.winner < next.rank later.loser := by
        intro later laterMember
        exact rankLt later (by simp [laterMember])
      have tailSideOrder : ∀ later ∈ instructions,
          match later.side with
          | .left => later.loser.val < later.winner.val
          | .right => later.winner.val < later.loser.val := by
        intro later laterMember
        exact sideOrder later (by simp [laterMember])
      rw [reparentMany]
      intro element owner parentEq
      have recursivelyOrdered :
          (reparentMany next instructions nextOrdered tailNotRoot tailRankLt
            tailSideOrder).HeapOrdered :=
        ih next nextOrdered tailNotRoot tailRankLt tailSideOrder
      have recursiveParent :
          (reparentMany next instructions nextOrdered tailNotRoot tailRankLt
            tailSideOrder).parent element = some owner := by
        simpa [next, headNotRoot, headRankLt, headSideOrder] using parentEq
      have rankOrder := recursivelyOrdered recursiveParent
      exact rankOrder

/-- A vertex not selected as a loser keeps its parent through the complete
reparenting batch. -/
theorem reparentMany_parent_of_not_loser {n : ℕ} (view : HeapView n)
    (instructions : List (ReparentInstruction n))
    (ordered : view.HeapOrdered) (loserNotRoot) (rankLt) (sideOrder)
    (element : Element n)
    (notLoser : ∀ instruction ∈ instructions,
      element ≠ instruction.loser) :
    (reparentMany view instructions ordered loserNotRoot rankLt
      sideOrder).parent element = view.parent element := by
  induction instructions generalizing view with
  | nil => rfl
  | cons instruction instructions ih =>
      let headNotRoot := loserNotRoot instruction (by simp)
      let headRankLt := rankLt instruction (by simp)
      let headSideOrder := sideOrder instruction (by simp)
      let next := view.reparentOne instruction.winner instruction.loser
        instruction.side ordered headNotRoot headRankLt headSideOrder
      have nextOrdered : next.HeapOrdered :=
        view.reparentOne_heapOrdered instruction.winner instruction.loser
          instruction.side ordered headNotRoot headRankLt headSideOrder
      have tailNotRoot : ∀ later ∈ instructions,
          later.loser ≠ next.root := by
        intro later laterMember
        exact loserNotRoot later (by simp [laterMember])
      have tailRankLt : ∀ later ∈ instructions,
          next.rank later.winner < next.rank later.loser := by
        intro later laterMember
        exact rankLt later (by simp [laterMember])
      have tailSideOrder : ∀ later ∈ instructions,
          match later.side with
          | .left => later.loser.val < later.winner.val
          | .right => later.winner.val < later.loser.val := by
        intro later laterMember
        exact sideOrder later (by simp [laterMember])
      have tailNotLoser : ∀ later ∈ instructions,
          element ≠ later.loser := by
        intro later laterMember
        exact notLoser later (by simp [laterMember])
      rw [reparentMany]
      calc
        (reparentMany next instructions nextOrdered tailNotRoot tailRankLt
            tailSideOrder).parent element = next.parent element :=
          ih next nextOrdered tailNotRoot tailRankLt tailSideOrder
            tailNotLoser
        _ = view.parent element := by
          simp [next, notLoser instruction (by simp)]

/-- With duplicate-free loser identities, every selected loser ends below its
selected winner after the whole simultaneous batch. -/
theorem reparentMany_parent_of_mem {n : ℕ} (view : HeapView n)
    (instructions : List (ReparentInstruction n))
    (ordered : view.HeapOrdered) (loserNotRoot) (rankLt) (sideOrder)
    (losersNodup : (instructions.map ReparentInstruction.loser).Nodup)
    (selected : ReparentInstruction n) (selectedMember : selected ∈ instructions) :
    (reparentMany view instructions ordered loserNotRoot rankLt
      sideOrder).parent selected.loser = some selected.winner := by
  induction instructions generalizing view with
  | nil => simp at selectedMember
  | cons instruction instructions ih =>
      have nodupFacts := List.nodup_cons.mp (by
        simpa only [List.map_cons] using losersNodup)
      let headNotRoot := loserNotRoot instruction (by simp)
      let headRankLt := rankLt instruction (by simp)
      let headSideOrder := sideOrder instruction (by simp)
      let next := view.reparentOne instruction.winner instruction.loser
        instruction.side ordered headNotRoot headRankLt headSideOrder
      have nextOrdered : next.HeapOrdered :=
        view.reparentOne_heapOrdered instruction.winner instruction.loser
          instruction.side ordered headNotRoot headRankLt headSideOrder
      have tailNotRoot : ∀ later ∈ instructions,
          later.loser ≠ next.root := by
        intro later laterMember
        exact loserNotRoot later (by simp [laterMember])
      have tailRankLt : ∀ later ∈ instructions,
          next.rank later.winner < next.rank later.loser := by
        intro later laterMember
        exact rankLt later (by simp [laterMember])
      have tailSideOrder : ∀ later ∈ instructions,
          match later.side with
          | .left => later.loser.val < later.winner.val
          | .right => later.winner.val < later.loser.val := by
        intro later laterMember
        exact sideOrder later (by simp [laterMember])
      rw [reparentMany]
      simp only [List.mem_cons] at selectedMember
      rcases selectedMember with rfl | selectedTail
      · have headNotTail : ∀ later ∈ instructions,
            selected.loser ≠ later.loser := by
          intro later laterMember equal
          exact nodupFacts.1
            (List.mem_map.mpr ⟨later, laterMember, equal.symm⟩)
        rw [reparentMany_parent_of_not_loser next instructions nextOrdered
          tailNotRoot tailRankLt tailSideOrder selected.loser headNotTail]
        simp [next]
      · exact ih next nextOrdered tailNotRoot tailRankLt tailSideOrder
          nodupFacts.2 selectedTail

/-- A vertex not selected as a loser also keeps its side. -/
theorem reparentMany_side_of_not_loser {n : ℕ} (view : HeapView n)
    (instructions : List (ReparentInstruction n))
    (ordered : view.HeapOrdered) (loserNotRoot) (rankLt) (sideOrder)
    (element : Element n)
    (notLoser : ∀ instruction ∈ instructions,
      element ≠ instruction.loser) :
    (reparentMany view instructions ordered loserNotRoot rankLt
      sideOrder).side element = view.side element := by
  induction instructions generalizing view with
  | nil => rfl
  | cons instruction instructions ih =>
      let headNotRoot := loserNotRoot instruction (by simp)
      let headRankLt := rankLt instruction (by simp)
      let headSideOrder := sideOrder instruction (by simp)
      let next := view.reparentOne instruction.winner instruction.loser
        instruction.side ordered headNotRoot headRankLt headSideOrder
      have nextOrdered : next.HeapOrdered :=
        view.reparentOne_heapOrdered instruction.winner instruction.loser
          instruction.side ordered headNotRoot headRankLt headSideOrder
      have tailNotRoot : ∀ later ∈ instructions,
          later.loser ≠ next.root := by
        intro later laterMember
        exact loserNotRoot later (by simp [laterMember])
      have tailRankLt : ∀ later ∈ instructions,
          next.rank later.winner < next.rank later.loser := by
        intro later laterMember
        exact rankLt later (by simp [laterMember])
      have tailSideOrder : ∀ later ∈ instructions,
          match later.side with
          | .left => later.loser.val < later.winner.val
          | .right => later.winner.val < later.loser.val := by
        intro later laterMember
        exact sideOrder later (by simp [laterMember])
      have tailNotLoser : ∀ later ∈ instructions,
          element ≠ later.loser := by
        intro later laterMember
        exact notLoser later (by simp [laterMember])
      rw [reparentMany]
      calc
        (reparentMany next instructions nextOrdered tailNotRoot tailRankLt
            tailSideOrder).side element = next.side element :=
          ih next nextOrdered tailNotRoot tailRankLt tailSideOrder
            tailNotLoser
        _ = view.side element := by
          simp [next, notLoser instruction (by simp)]

/-- With duplicate-free loser identities, a selected loser receives exactly
the side specified by its instruction. -/
theorem reparentMany_side_of_mem {n : ℕ} (view : HeapView n)
    (instructions : List (ReparentInstruction n))
    (ordered : view.HeapOrdered) (loserNotRoot) (rankLt) (sideOrder)
    (losersNodup : (instructions.map ReparentInstruction.loser).Nodup)
    (selected : ReparentInstruction n) (selectedMember : selected ∈ instructions) :
    (reparentMany view instructions ordered loserNotRoot rankLt
      sideOrder).side selected.loser = selected.side := by
  induction instructions generalizing view with
  | nil => simp at selectedMember
  | cons instruction instructions ih =>
      have nodupFacts := List.nodup_cons.mp (by
        simpa only [List.map_cons] using losersNodup)
      let headNotRoot := loserNotRoot instruction (by simp)
      let headRankLt := rankLt instruction (by simp)
      let headSideOrder := sideOrder instruction (by simp)
      let next := view.reparentOne instruction.winner instruction.loser
        instruction.side ordered headNotRoot headRankLt headSideOrder
      have nextOrdered : next.HeapOrdered :=
        view.reparentOne_heapOrdered instruction.winner instruction.loser
          instruction.side ordered headNotRoot headRankLt headSideOrder
      have tailNotRoot : ∀ later ∈ instructions,
          later.loser ≠ next.root := by
        intro later laterMember
        exact loserNotRoot later (by simp [laterMember])
      have tailRankLt : ∀ later ∈ instructions,
          next.rank later.winner < next.rank later.loser := by
        intro later laterMember
        exact rankLt later (by simp [laterMember])
      have tailSideOrder : ∀ later ∈ instructions,
          match later.side with
          | .left => later.loser.val < later.winner.val
          | .right => later.winner.val < later.loser.val := by
        intro later laterMember
        exact sideOrder later (by simp [laterMember])
      rw [reparentMany]
      simp only [List.mem_cons] at selectedMember
      rcases selectedMember with rfl | selectedTail
      · have headNotTail : ∀ later ∈ instructions,
            selected.loser ≠ later.loser := by
          intro later laterMember equal
          exact nodupFacts.1
            (List.mem_map.mpr ⟨later, laterMember, equal.symm⟩)
        rw [reparentMany_side_of_not_loser next instructions nextOrdered
          tailNotRoot tailRankLt tailSideOrder selected.loser headNotTail]
        simp [next]
      · exact ih next nextOrdered tailNotRoot tailRankLt tailSideOrder
          nodupFacts.2 selectedTail

end HeapView

end Splay.Lazy

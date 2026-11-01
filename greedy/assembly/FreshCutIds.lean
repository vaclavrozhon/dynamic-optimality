import OrderedBlockCuts

/-!
Fresh logical instance identifiers for concrete cut passes. Reserved but
unused identifiers are not block births. Freshness and preservation of
old identifiers are proved separately from the geometric birth budget.
-/

namespace GreedyMerge.FreshIds

open OrderedBlocks
open scoped BigOperators

theorem cutList_id_origin (side : Bool) (cut fresh : ℕ) (blocks : List Frozen)
    (piece : Frozen) (member : piece ∈ cutList side cut fresh blocks) :
    (∃ old ∈ blocks, piece.id = old.id) ∨
      (fresh ≤ piece.id ∧ piece.id < fresh + 2 * blocks.length) := by
  classical
  induction blocks generalizing fresh with
  | nil => simp [cutList] at member
  | cons block rest ih =>
      rcases List.mem_append.mp member with atHead | later
      · by_cases straddles : Straddles cut block
        · simp only [cutBlock, straddles, if_pos, List.mem_cons, List.not_mem_nil, or_false] at atHead
          rcases atHead with rfl | rfl <;> right <;> simp only [List.length_cons] <;> omega
        · have equal : piece = block := by simpa [cutBlock, straddles] using atHead
          exact Or.inl ⟨block, List.mem_cons_self, congrArg Frozen.id equal⟩
      · rcases ih (fresh + 2) later with ⟨old, oldMember, equal⟩ | interval
        · exact Or.inl ⟨old, List.mem_cons_of_mem _ oldMember, equal⟩
        · right
          simp only [List.length_cons]
          omega

theorem cutList_ids_nodup (side : Bool) (cut fresh : ℕ) (blocks : List Frozen)
    (unique : (blocks.map Frozen.id).Nodup)
    (oldIds : ∀ block ∈ blocks, block.id < fresh) :
    ((cutList side cut fresh blocks).map Frozen.id).Nodup := by
  classical
  induction blocks generalizing fresh with
  | nil => simp [cutList]
  | cons block rest ih =>
      simp only [List.map_cons, List.nodup_cons] at unique
      have tail := ih (fresh + 2) unique.2 (fun old member =>
        lt_trans (oldIds old (List.mem_cons_of_mem _ member)) (by omega))
      have blockOld := oldIds block List.mem_cons_self
      have tailOrigin : ∀ id ∈ (cutList side cut (fresh + 2) rest).map Frozen.id,
          (∃ old ∈ rest, id = old.id) ∨ fresh + 2 ≤ id := by
        intro id member
        obtain ⟨piece, present, rfl⟩ := List.mem_map.mp member
        rcases cutList_id_origin side cut (fresh + 2) rest piece present with old | interval
        · exact Or.inl old
        · exact Or.inr interval.1
      simp only [cutList, List.map_append]
      by_cases straddles : Straddles cut block
      · simp only [cutBlock, straddles, if_pos, List.map_cons, List.map_nil,
          List.cons_append, List.nil_append, List.nodup_cons]
        refine ⟨?_, ?_, tail⟩
        · intro member
          rcases List.mem_cons.mp member with equal | member
          · omega
          · rcases tailOrigin fresh member with ⟨old, oldMember, equal⟩ | lower
            · have bound := oldIds old (List.mem_cons_of_mem _ oldMember)
              omega
            · omega
        · intro member
          rcases tailOrigin (fresh + 1) member with ⟨old, oldMember, equal⟩ | lower
          · have bound := oldIds old (List.mem_cons_of_mem _ oldMember)
            omega
          · omega
      · simp only [cutBlock, if_neg straddles, List.map_cons, List.map_nil,
          List.cons_append, List.nil_append, List.nodup_cons]
        refine ⟨?_, tail⟩
        intro member
        rcases tailOrigin block.id member with ⟨old, oldMember, equal⟩ | lower
        · exact unique.1 (List.mem_map.mpr ⟨old, oldMember, equal.symm⟩)
        · omega

/-- Equal-width intervals assigned to different finite slots are disjoint. -/
theorem reserve_disjoint {start width first second x y : ℕ}
    (different : first ≠ second)
    (firstLower : start + width * first ≤ x)
    (firstUpper : x < start + width * first + width)
    (secondLower : start + width * second ≤ y)
    (secondUpper : y < start + width * second + width) : x ≠ y := by
  intro equal
  subst y
  rcases lt_or_gt_of_ne different with before | after
  · have order := Nat.mul_le_mul_left width (Nat.succ_le_of_lt before)
    nlinarith
  · have order := Nat.mul_le_mul_left width (Nat.succ_le_of_lt after)
    nlinarith

/-- A finite batch of lists may share one fresh counter. Slot intervals
reserve two names per old block, while the geometric cut code counts only
the fragments it actually creates. -/
theorem cutBatch_ids_disjoint {slots : ℕ} (side : Fin slots → Bool) (cut start width : ℕ)
    (blocks : Fin slots → List Frozen)
    (capacity : ∀ slot, 2 * (blocks slot).length ≤ width)
    (oldIds : ∀ slot block, block ∈ blocks slot → block.id < start)
    (disjoint : ∀ first second, first ≠ second →
      ∀ a ∈ blocks first, ∀ b ∈ blocks second, a.id ≠ b.id)
    (first second : Fin slots) (different : first ≠ second)
    (a : Frozen) (firstMember : a ∈ cutList (side first) cut (start + width * first.val) (blocks first))
    (b : Frozen) (secondMember : b ∈ cutList (side second) cut (start + width * second.val) (blocks second)) :
    a.id ≠ b.id := by
  have firstOrigin := cutList_id_origin (side first) cut _ _ a firstMember
  have secondOrigin := cutList_id_origin (side second) cut _ _ b secondMember
  rcases firstOrigin with ⟨oldA, oldAMember, equalA⟩ | firstRange
  · rcases secondOrigin with ⟨oldB, oldBMember, equalB⟩ | secondRange
    · simpa only [equalA, equalB] using disjoint first second different oldA oldAMember oldB oldBMember
    · have oldBound := oldIds first oldA oldAMember
      omega
  · rcases secondOrigin with ⟨oldB, oldBMember, equalB⟩ | secondRange
    · have oldBound := oldIds second oldB oldBMember
      omega
    · apply reserve_disjoint (start:=start) (width:=width)
        (first:=first.val) (second:=second.val) (fun equal => different (Fin.ext equal))
        firstRange.1 ?_ secondRange.1 ?_
      · have size := capacity first
        omega
      · have size := capacity second
        omega

theorem cutBatch_ids_below_next {slots : ℕ} (side : Fin slots → Bool) (cut start width : ℕ)
    (blocks : Fin slots → List Frozen) (_positiveWidth : 0 < width)
    (capacity : ∀ slot, 2 * (blocks slot).length ≤ width)
    (oldIds : ∀ slot block, block ∈ blocks slot → block.id < start)
    (slot : Fin slots) (piece : Frozen)
    (member : piece ∈ cutList (side slot) cut (start + width * slot.val) (blocks slot)) :
    piece.id < start + width * slots := by
  rcases cutList_id_origin (side slot) cut _ _ piece member with ⟨old, oldMember, equal⟩ | interval
  · have oldBound := oldIds slot old oldMember
    omega
  · have size := capacity slot
    have index := Nat.mul_le_mul_left width (Nat.succ_le_of_lt slot.isLt)
    nlinarith

def reserveWidth {slots : ℕ} (blocks : Fin slots → List Frozen) : ℕ :=
  2 * (1 + ∑ slot, (blocks slot).length)

theorem reserveWidth_positive {slots : ℕ} (blocks : Fin slots → List Frozen) :
    0 < reserveWidth blocks := by
  unfold reserveWidth
  omega

theorem reserveWidth_capacity {slots : ℕ} (blocks : Fin slots → List Frozen)
    (slot : Fin slots) : 2 * (blocks slot).length ≤ reserveWidth blocks := by
  have one : (blocks slot).length ≤ ∑ index, (blocks index).length :=
    Finset.single_le_sum (fun index _ => Nat.zero_le (blocks index).length) (Finset.mem_univ slot)
  unfold reserveWidth
  omega

/-- A deterministic fresh pass on a finite collection of side lists.
The second component is the next unused identifier, not the birth count. -/
noncomputable def freshPass {slots : ℕ} (side : Fin slots → Bool) (cut start : ℕ)
    (blocks : Fin slots → List Frozen) : (Fin slots → List Frozen) × ℕ :=
  (fun slot => cutList (side slot) cut (start + reserveWidth blocks * slot.val) (blocks slot),
   start + reserveWidth blocks * slots)

theorem freshPass_spec {slots : ℕ} (side : Fin slots → Bool) (cut start : ℕ)
    (blocks : Fin slots → List Frozen)
    (unique : ∀ slot, ((blocks slot).map Frozen.id).Nodup)
    (oldIds : ∀ slot block, block ∈ blocks slot → block.id < start)
    (disjoint : ∀ first second, first ≠ second →
      ∀ a ∈ blocks first, ∀ b ∈ blocks second, a.id ≠ b.id) :
    let result := freshPass side cut start blocks
    (∀ slot, ((result.1 slot).map Frozen.id).Nodup) ∧
    (∀ first second, first ≠ second →
      ∀ a ∈ result.1 first, ∀ b ∈ result.1 second, a.id ≠ b.id) ∧
    (∀ slot piece, piece ∈ result.1 slot → piece.id < result.2) ∧
    start ≤ result.2 := by
  dsimp only [freshPass]
  refine ⟨?_, ?_, ?_, Nat.le_add_right _ _⟩
  · intro slot
    apply cutList_ids_nodup _ _ _ _ (unique slot)
    intro block member
    have old := oldIds slot block member
    omega
  · intro first second different a firstMember b secondMember
    exact cutBatch_ids_disjoint side cut start _ blocks (reserveWidth_capacity blocks)
      oldIds disjoint first second different a firstMember b secondMember
  · intro slot piece member
    exact cutBatch_ids_below_next side cut start _ blocks (reserveWidth_positive blocks)
      (reserveWidth_capacity blocks) oldIds slot piece member

end GreedyMerge.FreshIds

#print axioms GreedyMerge.FreshIds.cutList_ids_nodup
#print axioms GreedyMerge.FreshIds.cutBatch_ids_disjoint
#print axioms GreedyMerge.FreshIds.cutBatch_ids_below_next
#print axioms GreedyMerge.FreshIds.freshPass_spec

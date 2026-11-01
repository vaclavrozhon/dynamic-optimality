import Splay.Lazy.Model

namespace Splay.Accounting

/--
The index of the first complete four-child double-rotation group contained
in an interval beginning at `start` in bottom-up order.

Every splay double step consumes two consecutive hit internal nodes, and
each hit internal node contributes two light children.  Thus the natural
geometric groups have size four.  Rounding `start` up to the next multiple
of four discards at most three children at the lower boundary.
-/
def firstCompleteDoubleGroup (start : ℕ) : ℕ :=
  (start + 3) / 4

/--
Number of complete four-child double-rotation groups wholly contained in
the half-open interval `[start, start + length)`.
-/
def completeDoubleGroupCount (start length : ℕ) : ℕ :=
  (start + length) / 4 - firstCompleteDoubleGroup start

/-- Concrete group indices selected by `completeDoubleGroupCount`. -/
def completeDoubleGroups (start length : ℕ) : List ℕ :=
  (List.range (completeDoubleGroupCount start length)).map
    (firstCompleteDoubleGroup start + ·)

@[simp]
theorem length_completeDoubleGroups (start length : ℕ) :
    (completeDoubleGroups start length).length =
      completeDoubleGroupCount start length := by
  simp [completeDoubleGroups]

theorem mem_completeDoubleGroups_iff {start length group : ℕ} :
    group ∈ completeDoubleGroups start length ↔
      firstCompleteDoubleGroup start ≤ group ∧
        group < firstCompleteDoubleGroup start +
          completeDoubleGroupCount start length := by
  simp only [completeDoubleGroups, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨offset, offsetLt, rfl⟩
    omega
  · rintro ⟨lower, upper⟩
    refine ⟨group - firstCompleteDoubleGroup start, ?_, ?_⟩
    · omega
    · omega

/-- A selected group starts no earlier than the interval. -/
theorem start_le_four_mul_of_mem_completeDoubleGroups
    {start length group : ℕ}
    (member : group ∈ completeDoubleGroups start length) :
    start ≤ 4 * group := by
  rw [mem_completeDoubleGroups_iff] at member
  unfold firstCompleteDoubleGroup at member
  omega

/-- A selected group ends no later than the interval. -/
theorem four_mul_add_four_le_end_of_mem_completeDoubleGroups
    {start length group : ℕ}
    (member : group ∈ completeDoubleGroups start length) :
    4 * group + 4 ≤ start + length := by
  rw [mem_completeDoubleGroups_iff] at member
  unfold completeDoubleGroupCount firstCompleteDoubleGroup at member
  omega

/-- Distinct selected double groups have distinct global indices. -/
theorem completeDoubleGroups_nodup (start length : ℕ) :
    (completeDoubleGroups start length).Nodup := by
  unfold completeDoubleGroups
  exact
    List.Nodup.map
      (by intro first second equal; exact Nat.add_left_cancel equal)
      List.nodup_range

/--
The exact arithmetic core of `lemma:internal-pairings-fraction`.

At most three children precede the first complete group and at most three
follow the last complete group.  Consequently all but six children of an
arbitrary contiguous interval belong to complete four-child groups.
-/
theorem interval_length_le_four_mul_completeDoubleGroupCount_add_six
    (start length : ℕ) :
    length ≤ 4 * completeDoubleGroupCount start length + 6 := by
  unfold completeDoubleGroupCount firstCompleteDoubleGroup
  omega

/-- Per-phase lower bound in the division form used by the manuscript. -/
theorem sub_six_div_four_le_completeDoubleGroupCount
    (start length : ℕ) :
    (length - 6) / 4 ≤ completeDoubleGroupCount start length := by
  unfold completeDoubleGroupCount firstCompleteDoubleGroup
  omega

/--
List-segment form of the same estimate.  `front.length` is the global
bottom-up offset of the lazy interval, and every selected index denotes a
complete double-rotation group wholly inside that interval.
-/
theorem IsSegment.exists_completeDoubleGroups
    {α : Type*} {inside whole : List α}
    (segment : Splay.Lazy.IsSegment inside whole) :
    ∃ front back,
      whole = front ++ inside ++ back ∧
        (inside.length - 6) / 4 ≤
          (completeDoubleGroups front.length inside.length).length ∧
        (∀ group ∈ completeDoubleGroups front.length inside.length,
          front.length ≤ 4 * group ∧
            4 * group + 4 ≤ front.length + inside.length) := by
  obtain ⟨front, back, decomposition⟩ := segment
  refine ⟨front, back, decomposition, ?_, ?_⟩
  · rw [length_completeDoubleGroups]
    exact sub_six_div_four_le_completeDoubleGroupCount _ _
  · intro group member
    exact
      ⟨start_le_four_mul_of_mem_completeDoubleGroups member,
        four_mul_add_four_le_end_of_mem_completeDoubleGroups member⟩

/--
Every one of the four ambient positions of a selected complete group is an
actual element of the represented segment.  This is the list-level meaning
of the manuscript phrase “the zig-zig is internal to the interval”.
-/
theorem getElem?_mem_of_completeDoubleGroup
    {α : Type*} {inside whole front back : List α}
    (decomposition : whole = front ++ inside ++ back)
    {group offset : ℕ}
    (groupMember :
      group ∈ completeDoubleGroups front.length inside.length)
    (offsetLt : offset < 4) :
    ∃ element,
      whole[4 * group + offset]? = some element ∧ element ∈ inside := by
  have groupStart :=
    start_le_four_mul_of_mem_completeDoubleGroups groupMember
  have groupEnd :=
    four_mul_add_four_le_end_of_mem_completeDoubleGroups groupMember
  have insideIndexLt :
      4 * group + offset - front.length < inside.length := by
    omega
  have normalized : whole = front ++ (inside ++ back) := by
    rw [decomposition]
    simp only [List.append_assoc]
  refine ⟨inside[4 * group + offset - front.length], ?_,
    List.getElem_mem insideIndexLt⟩
  rw [normalized]
  rw [List.getElem?_append_right (by omega)]
  rw [List.getElem?_append_left insideIndexLt]
  exact List.getElem?_eq_getElem insideIndexLt

end Splay.Accounting

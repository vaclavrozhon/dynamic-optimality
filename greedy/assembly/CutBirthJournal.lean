import FreshCutIds

/-!
Only actual instance births enter the journal. Reserving an identifier
interval is an implementation detail and does not enlarge the finite Block
type of the accounting theorem. The journal supports all produced ids and
its literal length equals the previously derived geometric birth count.
-/

namespace GreedyMerge.BirthJournal

open OrderedBlocks FreshIds

noncomputable def cutBirthIds (cut : ℕ) : ℕ → List Frozen → List ℕ
  | _, [] => []
  | fresh, block :: rest =>
      (if Straddles cut block then [fresh, fresh + 1] else []) ++
        cutBirthIds cut (fresh + 2) rest

theorem cutBirthIds_length (cut fresh : ℕ) (blocks : List Frozen) :
    (cutBirthIds cut fresh blocks).length = cutListBirths cut blocks := by
  classical
  induction blocks generalizing fresh with
  | nil => rfl
  | cons block rest ih =>
      simp only [cutBirthIds, List.length_append, cutListBirths, ih, cutBlockBirths]
      split_ifs <;> rfl

theorem cutBirthIds_sublist (side : Bool) (cut fresh : ℕ) (blocks : List Frozen) :
    (cutBirthIds cut fresh blocks).Sublist ((cutList side cut fresh blocks).map Frozen.id) := by
  classical
  induction blocks generalizing fresh with
  | nil => exact .refl _
  | cons block rest ih =>
      simp only [cutBirthIds, cutList, List.map_append]
      by_cases crossing : Straddles cut block
      · simp only [if_pos crossing, cutBlock, List.map_cons, List.map_nil]
        exact (List.Sublist.refl [fresh, fresh + 1]).append (ih (fresh + 2))
      · simp only [if_neg crossing, cutBlock, List.map_cons, List.map_nil]
        exact (List.nil_sublist _).append (ih (fresh + 2))

theorem cutBirthIds_nodup (side : Bool) (cut fresh : ℕ) (blocks : List Frozen)
    (unique : (blocks.map Frozen.id).Nodup)
    (oldIds : ∀ block ∈ blocks, block.id < fresh) :
    (cutBirthIds cut fresh blocks).Nodup :=
  (cutList_ids_nodup side cut fresh blocks unique oldIds).sublist
    (cutBirthIds_sublist side cut fresh blocks)

theorem cutBirthIds_range (cut fresh : ℕ) (blocks : List Frozen) (id : ℕ)
    (member : id ∈ cutBirthIds cut fresh blocks) :
    fresh ≤ id ∧ id < fresh + 2 * blocks.length := by
  classical
  induction blocks generalizing fresh with
  | nil => simp [cutBirthIds] at member
  | cons block rest ih =>
      rcases List.mem_append.mp member with head | tail
      · by_cases crossing : Straddles cut block
        · simp only [if_pos crossing, List.mem_cons, List.not_mem_nil, or_false] at head
          rcases head with rfl | rfl <;> simp only [List.length_cons] <;> omega
        · simp only [if_neg crossing, List.not_mem_nil] at head
      · have bound := ih (fresh + 2) tail
        simp only [List.length_cons]
        omega

/-- Every post-pass logical instance is either an exact retained old id
or an id actually appended to the birth journal. -/
theorem cut_output_supported (side : Bool) (cut fresh : ℕ) (blocks : List Frozen)
    (piece : Frozen) (member : piece ∈ cutList side cut fresh blocks) :
    piece.id ∈ blocks.map Frozen.id ∨ piece.id ∈ cutBirthIds cut fresh blocks := by
  classical
  induction blocks generalizing fresh with
  | nil => simp [cutList] at member
  | cons block rest ih =>
      rcases List.mem_append.mp member with head | tail
      · by_cases crossing : Straddles cut block
        · simp only [cutBlock, if_pos crossing, List.mem_cons, List.not_mem_nil, or_false] at head
          right
          simp only [cutBirthIds, if_pos crossing, List.mem_append, List.mem_cons,
            List.not_mem_nil, or_false]
          rcases head with rfl | rfl <;> simp
        · have equal : piece = block := by simpa only [cutBlock, if_neg crossing, List.mem_singleton] using head
          left
          subst piece
          simp
      · rcases ih (fresh + 2) tail with old | born
        · left
          exact List.mem_cons_of_mem _ old
        · right
          exact List.mem_append_right _ born

abbrev Born (ids : List ℕ) := {id : ℕ // id ∈ ids.toFinset}

/-- The finite accounting Block universe counts born ids, never the
possibly much larger upper bound used to reserve names. -/
theorem born_card_le_births (ids : List ℕ) : Fintype.card (Born ids) ≤ ids.length := by
  simpa only [Born, Fintype.card_coe] using List.toFinset_card_le ids

theorem cut_born_card_le_budget (cut fresh : ℕ) (blocks : List Frozen) :
    Fintype.card (Born (cutBirthIds cut fresh blocks)) ≤ cutListBirths cut blocks := by
  rw [← cutBirthIds_length cut fresh blocks]
  exact born_card_le_births _

end GreedyMerge.BirthJournal

#print axioms GreedyMerge.BirthJournal.cut_output_supported
#print axioms GreedyMerge.BirthJournal.cut_born_card_le_budget

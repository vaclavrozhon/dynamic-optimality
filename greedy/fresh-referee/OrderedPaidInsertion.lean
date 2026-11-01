import OrderedOuterTransfer

/-!
A total arbitrary-position paid insertion for a valid ordered side list.
The needed position and at-most-one split are computed from the new key,
not supplied as an insertion certificate. Old joined records are retained.
-/
namespace GreedyMerge.OrderedBlocks

open GreedyMerge.Primitives (Entry)

noncomputable def installPaid (owner : ℕ) (side : Bool)
    (splitFresh paidId paidFamily base : ℕ) (entry : Entry) (state : SideState) : SideState :=
  let parts := separateOuter side entry.key splitFresh state
  ⟨parts.1 ++ [singleton paidId paidFamily owner base entry] ++ parts.2, state.grower⟩

theorem installPaid_entries (owner : ℕ) (side : Bool)
    (splitFresh paidId paidFamily base : ℕ) (entry : Entry) (state : SideState) :
    entries (installPaid owner side splitFresh paidId paidFamily base entry state) =
      frozenEntries (separateOuter side entry.key splitFresh state).1 ++
        entry :: (frozenEntries (separateOuter side entry.key splitFresh state).2 ++
          growerEntries state.grower) := by
  simp [installPaid, entries, singleton, frozenEntries, List.append_assoc]

/-- A new key can be inserted at its unique ordered position after the
receiving grower is sealed. No insertion-position premise is needed. -/
theorem installPaid_valid (owner : ℕ) (side : Bool)
    (splitFresh paidId paidFamily base : ℕ) (entry : Entry) (state : SideState)
    (valid : Valid owner side state) (empty : growerEntries state.grower = [])
    (entrySide : onSide owner side entry)
    (newKey : ∀ old ∈ entries state, old.key ≠ entry.key) :
    Valid owner side (installPaid owner side splitFresh paidId paidFamily base entry state) := by
  let parts := separateOuter side entry.key splitFresh state
  have partition := separateOuter_entries side entry.key splitFresh state valid
  have oldEntries : entries state = frozenEntries parts.1 ++ frozenEntries parts.2 := by
    simp only [entries, empty, List.append_nil]
    exact partition.symm
  have oldOrder := valid.1
  rw [oldEntries, List.pairwise_append] at oldOrder
  have leftOrder : ∀ old ∈ frozenEntries parts.1, outward side old entry := by
    intro old member
    have insideCut := separateOuter_inside side entry.key splitFresh state old member
    have different := newKey old (by rw [oldEntries]; exact List.mem_append_left _ member)
    cases side with
    | false =>
        change old.key < entry.key
        simpa only [cutPrefix, Bool.false_eq_true, ↓reduceIte, decide_eq_true_eq] using insideCut
    | true =>
        change entry.key < old.key
        have le : entry.key ≤ old.key := by
          simpa only [cutPrefix, ↓reduceIte, decide_eq_true_eq] using insideCut
        omega
  have rightOrder : ∀ old ∈ frozenEntries parts.2, outward side entry old := by
    intro old member
    have outside := separateOuter_outside side entry.key splitFresh state valid old member
    have different := newKey old (by rw [oldEntries]; exact List.mem_append_right _ member)
    cases side with
    | false =>
        change entry.key < old.key
        have le : entry.key ≤ old.key := by
          simpa only [cutPrefix, Bool.false_eq_true, ↓reduceIte, decide_eq_false_iff_not,
            Nat.not_lt] using outside
        omega
    | true =>
        change old.key < entry.key
        simpa only [cutPrefix, ↓reduceIte, decide_eq_false_iff_not, Nat.not_le] using outside
  have newEntries : entries (installPaid owner side splitFresh paidId paidFamily base entry state) =
      frozenEntries parts.1 ++ entry :: frozenEntries parts.2 := by
    simpa only [empty, List.append_nil] using
      installPaid_entries owner side splitFresh paidId paidFamily base entry state
  refine ⟨?_, ?_, valid.2.2⟩
  · rw [newEntries]
    apply List.pairwise_append.mpr
    refine ⟨oldOrder.1, List.pairwise_cons.mpr ⟨rightOrder, oldOrder.2.1⟩, ?_⟩
    intro first firstMem second secondMem
    rcases List.mem_cons.mp secondMem with rfl | secondMem
    · exact leftOrder first firstMem
    · exact oldOrder.2.2 first firstMem second secondMem
  · intro old member
    rw [newEntries] at member
    rcases List.mem_append.mp member with member | member
    · exact valid.2.1 old (by rw [oldEntries]; exact List.mem_append_left _ member)
    · rcases List.mem_cons.mp member with rfl | member
      · exact entrySide
      · exact valid.2.1 old (by rw [oldEntries]; exact List.mem_append_right _ member)

/-- Conversion does not change any old Entry; its only new instance is the
empty replacement grower. Then the key-directed split and singleton finish
one paid insertion with at most four receiving-side births. -/
noncomputable def paidInsertion (owner : ℕ) (side : Bool)
    (replacementFamily replacementId splitFresh paidId paidFamily base : ℕ)
    (entry : Entry) (state : SideState) : SideState :=
  installPaid owner side splitFresh paidId paidFamily base entry
    (convert owner replacementFamily replacementId base state)

noncomputable def paidInsertionBirths (owner : ℕ)
    (replacementFamily replacementId base : ℕ) (entry : Entry) (state : SideState) : ℕ :=
  conversionBirths state +
    cutListBirths entry.key (convert owner replacementFamily replacementId base state).shrinking + 1

theorem converted_grower_empty (owner family id base : ℕ) (state : SideState) :
    growerEntries (convert owner family id base state).grower = [] := by
  cases same : state.grower with
  | none => simp [convert, same, growerEntries]
  | some old =>
      by_cases empty : old.members = []
      · simp [convert, same, empty, growerEntries]
      · simp [convert, same, empty, growerEntries, emptyGrower]

theorem conversionBirths_le_one (state : SideState) : conversionBirths state ≤ 1 := by
  cases same : state.grower with
  | none => simp [conversionBirths, same]
  | some old => simp only [conversionBirths, same]; split_ifs <;> omega

theorem paidInsertion_valid (owner : ℕ) (side : Bool)
    (replacementFamily replacementId splitFresh paidId paidFamily base : ℕ)
    (entry : Entry) (state : SideState)
    (valid : Valid owner side state) (entrySide : onSide owner side entry)
    (newKey : ∀ old ∈ entries state, old.key ≠ entry.key) :
    Valid owner side (paidInsertion owner side replacementFamily replacementId splitFresh
      paidId paidFamily base entry state) := by
  apply installPaid_valid
  · exact conversion_valid owner replacementFamily replacementId base side state valid
  · exact converted_grower_empty ..
  · exact entrySide
  · simpa only [conversion_entries] using newKey

theorem paidInsertion_births_le_four (owner : ℕ) (side : Bool)
    (replacementFamily replacementId base : ℕ) (entry : Entry) (state : SideState)
    (valid : Valid owner side state) :
    paidInsertionBirths owner replacementFamily replacementId base entry state ≤ 4 := by
  have conversion := conversionBirths_le_one state
  have split := cutState_births_le_two side entry.key
    (convert owner replacementFamily replacementId base state)
    (conversion_valid owner replacementFamily replacementId base side state valid)
  unfold paidInsertionBirths
  omega

/-- Every old history record survives verbatim; the only additional Entry
is the explicitly supplied paid event record. -/
theorem paidInsertion_history_perm (owner : ℕ) (side : Bool)
    (replacementFamily replacementId splitFresh paidId paidFamily base : ℕ)
    (entry : Entry) (state : SideState) (valid : Valid owner side state) :
    (entries (paidInsertion owner side replacementFamily replacementId splitFresh
      paidId paidFamily base entry state)).Perm (entry :: entries state) := by
  let converted := convert owner replacementFamily replacementId base state
  have convertedValid := conversion_valid owner replacementFamily replacementId base side state valid
  have partition := separateOuter_entries side entry.key splitFresh converted convertedValid
  have empty := converted_grower_empty owner replacementFamily replacementId base state
  change (entries (installPaid owner side splitFresh paidId paidFamily base entry converted)).Perm _
  rw [installPaid_entries, empty, List.append_nil]
  have swap : (frozenEntries (separateOuter side entry.key splitFresh converted).1 ++ [entry]).Perm
      ([entry] ++ frozenEntries (separateOuter side entry.key splitFresh converted).1) :=
    List.perm_append_comm
  have perm := swap.append_right (frozenEntries (separateOuter side entry.key splitFresh converted).2)
  have oldEntries : frozenEntries converted.shrinking = entries state := by
    rw [←conversion_entries owner replacementFamily replacementId base state]
    change frozenEntries converted.shrinking = frozenEntries converted.shrinking ++ growerEntries converted.grower
    rw [empty, List.append_nil]
  simpa only [List.append_assoc, List.singleton_append, List.cons_append, List.nil_append, partition, oldEntries] using perm

#print axioms paidInsertion_valid
#print axioms paidInsertion_births_le_four
#print axioms paidInsertion_history_perm

end GreedyMerge.OrderedBlocks

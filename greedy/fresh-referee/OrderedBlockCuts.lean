import OrderedBlockPrimitives
import AdminCutCensus

/-!
Cut preparation for actual ordered block states. A straddling block is
identified from its concrete immutable member list, and the support map is
proved from actual canonical heap parents and comparator cut geometry.
No aggregate split bound is an input to these results.
-/
namespace GreedyMerge.OrderedBlocks

open GreedyMerge.Primitives (Entry)
open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Lazy.Canonical
open GreedyMerge.AdminCuts

/-- Both sides of the natural-order cut occur among this block's members. -/
def Straddles (cut : ℕ) (block : Frozen) : Prop :=
  (∃ first ∈ block.members, first.key < cut) ∧
  (∃ second ∈ block.members, cut ≤ second.key)

instance straddlesDecidable (cut : ℕ) (block : Frozen) : Decidable (Straddles cut block) := by
  unfold Straddles
  infer_instance

theorem frozen_member_entries {state : SideState} {block : Frozen}
    (blockMem : block ∈ state.shrinking) {entry : Entry}
    (entryMem : entry ∈ block.members) : entry ∈ entries state := by
  apply List.mem_append_left
  exact List.mem_flatMap.mpr ⟨block, blockMem, entryMem⟩

theorem ordered_blocks {owner : ℕ} {goLeft : Bool} {state : SideState}
    (valid : Valid owner goLeft state) :
    state.shrinking.Pairwise
      (fun first second => ∀ x ∈ first.members, ∀ y ∈ second.members, outward goLeft x y) := by
  have inside := (List.pairwise_append.mp valid.1).1
  exact (List.pairwise_flatMap.mp inside).2

theorem straddlers_not_ordered {cut : ℕ} {goLeft : Bool} {first second : Frozen}
    (firstCut : Straddles cut first) (secondCut : Straddles cut second) :
    ¬ (∀ x ∈ first.members, ∀ y ∈ second.members, outward goLeft x y) := by
  intro ordered
  obtain ⟨leftFirst, leftMem, leftLt⟩ := firstCut.1
  obtain ⟨rightFirst, rightMem, rightLe⟩ := firstCut.2
  obtain ⟨leftSecond, leftMem', leftLt'⟩ := secondCut.1
  obtain ⟨rightSecond, rightMem', rightLe'⟩ := secondCut.2
  cases goLeft with
  | false =>
      have h := ordered rightFirst rightMem leftSecond leftMem'
      simp only [outward, Bool.false_eq_true, ↓reduceIte] at h
      omega
  | true =>
      have h := ordered leftFirst leftMem rightSecond rightMem'
      simp only [outward, ↓reduceIte] at h
      omega

/-- The concrete strict side order permits at most one straddling block. -/
theorem straddling_index_unique {owner cut : ℕ} {goLeft : Bool} {state : SideState}
    (valid : Valid owner goLeft state)
    (first second : Fin state.shrinking.length)
    (firstCut : Straddles cut (state.shrinking.get first))
    (secondCut : Straddles cut (state.shrinking.get second)) : first = second := by
  by_contra different
  rcases lt_or_gt_of_ne different with less | greater
  · exact straddlers_not_ordered firstCut secondCut
      ((ordered_blocks valid).rel_get_of_lt less)
  · exact straddlers_not_ordered secondCut firstCut
      ((ordered_blocks valid).rel_get_of_lt greater)

/-- A straddler is necessarily on a uniquely determined side of its owner. -/
theorem straddling_side {owner cut : ℕ} {goLeft : Bool} {state : SideState}
    (valid : Valid owner goLeft state) {block : Frozen}
    (member : block ∈ state.shrinking) (cross : Straddles cut block) :
    goLeft = decide (cut ≤ owner) := by
  obtain ⟨first, firstMem, firstLt⟩ := cross.1
  obtain ⟨second, secondMem, secondGe⟩ := cross.2
  have firstSide := valid.2.1 first (frozen_member_entries member firstMem)
  have secondSide := valid.2.1 second (frozen_member_entries member secondMem)
  cases goLeft with
  | false =>
      simp only [onSide, Bool.false_eq_true, ↓reduceIte] at firstSide secondSide
      have h : ¬ cut ≤ owner := by omega
      simp [h]
  | true =>
      simp only [onSide, ↓reduceIte] at firstSide secondSide
      have h : cut ≤ owner := by omega
      simp [h]

/-- The block state's member lists are actual old canonical children. -/
def ParentSound {n : ℕ} (snapshot : Snapshot n) (tree : BST 0 n)
    (owner : External n) (state : SideState) : Prop :=
  ∀ entry ∈ entries state, ∃ record : External n,
    record.val = entry.key ∧ canonicalParent snapshot tree record = some owner

/-- Every concrete straddling block produces one of the independently
bounded cut/owner incidences of the actual comparator rotation. -/
theorem straddling_supported {n depth : ℕ} {before after : BST 0 n}
    (profile : RotationCutProfile before after depth) (tree : BST 0 n)
    {entry : ℕ × ℕ} (entryMem : entry ∈ profile.entries)
    {owner : External n} {state : SideState}
    (sound : ParentSound (Snapshot.ofTree before) tree owner state)
    {block : Frozen} (blockMem : block ∈ state.shrinking)
    (cross : Straddles entry.1 block) :
    (entry, owner) ∈ cutOwnerIncidences profile tree := by
  obtain ⟨first, firstMem, firstLt⟩ := cross.1
  obtain ⟨second, secondMem, secondGe⟩ := cross.2
  obtain ⟨firstRecord, firstKey, firstParent⟩ :=
    sound first (frozen_member_entries blockMem firstMem)
  obtain ⟨secondRecord, secondKey, secondParent⟩ :=
    sound second (frozen_member_entries blockMem secondMem)
  apply children_cut_supported profile tree entry entryMem firstParent secondParent
  rw [firstKey, secondKey]
  omega

/-- Occurrence identities use actual owner, side, and position, rather
than assuming that externally supplied block ids are unique. -/
abbrev BlockOccurrence {n : ℕ} (states : External n → Bool → SideState) :=
  Σ owner : External n, Σ side : Bool, Fin (states owner side).shrinking.length

def blockAt {n : ℕ} {states : External n → Bool → SideState}
    (occurrence : BlockOccurrence states) : Frozen :=
  (states occurrence.1 occurrence.2.1).shrinking.get occurrence.2.2

abbrev StraddlingOccurrence {n depth : ℕ} {before after : BST 0 n}
    (profile : RotationCutProfile before after depth)
    (states : External n → Bool → SideState) :=
  { occurrence : { entry // entry ∈ profile.entries.toFinset } × BlockOccurrence states //
    Straddles occurrence.1.val.1 (blockAt occurrence.2) }

noncomputable instance straddlingOccurrenceFintype {n depth : ℕ} {before after : BST 0 n}
    (profile : RotationCutProfile before after depth)
    (states : External n → Bool → SideState) :
    Fintype (StraddlingOccurrence profile states) := Fintype.ofFinite _

noncomputable def occurrenceSupport {n depth : ℕ} {before after : BST 0 n}
    (profile : RotationCutProfile before after depth) (tree : BST 0 n)
    (states : External n → Bool → SideState)
    (sound : ∀ owner side, ParentSound (Snapshot.ofTree before) tree owner (states owner side))
    (occurrence : StraddlingOccurrence profile states) :
    { pair // pair ∈ cutOwnerIncidences profile tree } := by
  refine ⟨(occurrence.val.1.val, occurrence.val.2.1), ?_⟩
  apply straddling_supported profile tree
    (List.mem_toFinset.mp occurrence.val.1.property)
    (sound occurrence.val.2.1 occurrence.val.2.2.1)
    (List.get_mem _ _)
  exact occurrence.property

/-- No two actual affected blocks charge the same cut/owner pair. The
side is forced by the cut position and the position by strict side order. -/
theorem occurrenceSupport_injective {n depth : ℕ} {before after : BST 0 n}
    (profile : RotationCutProfile before after depth) (tree : BST 0 n)
    (states : External n → Bool → SideState)
    (valid : ∀ owner side, Valid owner.val side (states owner side))
    (sound : ∀ owner side, ParentSound (Snapshot.ofTree before) tree owner (states owner side)) :
    Function.Injective (occurrenceSupport profile tree states sound) := by
  intro first second same
  rcases first with ⟨⟨⟨firstCut, firstCutMem⟩, ⟨firstOwner, firstSide, firstIndex⟩⟩, firstCross⟩
  rcases second with ⟨⟨⟨secondCut, secondCutMem⟩, ⟨secondOwner, secondSide, secondIndex⟩⟩, secondCross⟩
  have pairEq : (firstCut, firstOwner) = (secondCut, secondOwner) :=
    congrArg Subtype.val same
  obtain ⟨cutEq, ownerEq⟩ := Prod.mk.inj pairEq
  cases cutEq
  cases ownerEq
  have sideEq : firstSide = secondSide :=
    (straddling_side (valid firstOwner firstSide) (List.get_mem _ _) firstCross).trans
      (straddling_side (valid firstOwner secondSide) (List.get_mem _ _) secondCross).symm
  cases sideEq
  have indexEq : firstIndex = secondIndex :=
    straddling_index_unique (valid firstOwner firstSide) firstIndex secondIndex firstCross secondCross
  cases indexEq
  rfl

/-- The number of concrete straddling occurrences is bounded by the
actual cut geometry. This is derived, not supplied in the block contract. -/
theorem straddling_occurrences_card {n depth : ℕ} {before after : BST 0 n}
    (profile : RotationCutProfile before after depth) (tree : BST 0 n)
    (states : External n → Bool → SideState)
    (valid : ∀ owner side, Valid owner.val side (states owner side))
    (sound : ∀ owner side, ParentSound (Snapshot.ofTree before) tree owner (states owner side)) :
    Fintype.card (StraddlingOccurrence profile states) ≤ (depth + 2)^2 := by
  classical
  have card := Fintype.card_le_of_injective _
    (occurrenceSupport_injective profile tree states valid sound)
  exact card.trans (by simpa using cut_owner_incidence_card profile tree)

/-- The part before a cut in the side's inner-to-outer order. -/
def cutPrefix (goLeft : Bool) (cut : ℕ) (entry : Entry) : Bool :=
  if goLeft then decide (cut ≤ entry.key) else decide (entry.key < cut)

theorem cutPrefix_order {goLeft : Bool} {cut : ℕ} {first second : Entry}
    (ordered : outward goLeft first second) (inside : cutPrefix goLeft cut second = true) :
    cutPrefix goLeft cut first = true := by
  cases goLeft <;> simp_all [outward, cutPrefix] <;> omega

theorem dropWhile_cutPrefix_false {goLeft : Bool} {cut : ℕ} {members : List Entry}
    (ordered : members.Pairwise (outward goLeft)) :
    ∀ entry ∈ members.dropWhile (cutPrefix goLeft cut), cutPrefix goLeft cut entry = false := by
  induction members with
  | nil => simp
  | cons first rest ih =>
      obtain ⟨firstOrder, restOrder⟩ := List.pairwise_cons.mp ordered
      by_cases firstInside : cutPrefix goLeft cut first = true
      · simpa [List.dropWhile_cons, firstInside] using ih restOrder
      · have firstOutside : cutPrefix goLeft cut first = false := by
          cases h : cutPrefix goLeft cut first <;> simp_all
        intro entry member
        have casesMember : entry = first ∨ entry ∈ rest := by
          simpa [List.dropWhile_cons, firstOutside] using member
        rcases casesMember with rfl | member
        · exact firstOutside
        · cases value : cutPrefix goLeft cut entry with
          | false => rfl
          | true => exact False.elim (firstInside (cutPrefix_order (firstOrder entry member) value))

noncomputable def cutBlock (goLeft : Bool) (cut leftId rightId : ℕ) (block : Frozen) : List Frozen :=
  if Straddles cut block then
    [{ block with id := leftId, members := block.members.takeWhile (cutPrefix goLeft cut) },
     { block with id := rightId, members := block.members.dropWhile (cutPrefix goLeft cut) }]
  else [block]

noncomputable def cutBlockBirths (cut : ℕ) (block : Frozen) : ℕ :=
  if Straddles cut block then 2 else 0

/-- A real cut keeps every immutable Entry record in exactly the same
flattened order. Both split fragments carry fresh supplied logical ids. -/
theorem cutBlock_entries (goLeft : Bool) (cut leftId rightId : ℕ) (block : Frozen) :
    frozenEntries (cutBlock goLeft cut leftId rightId block) = block.members := by
  classical
  unfold cutBlock
  split_ifs <;> simp [frozenEntries]

theorem cutBlock_births (goLeft : Bool) (cut leftId rightId : ℕ) (block : Frozen) :
    cutBlockBirths cut block =
      if Straddles cut block then (cutBlock goLeft cut leftId rightId block).length else 0 := by
  classical
  unfold cutBlockBirths cutBlock
  split_ifs <;> rfl

/-- Cutting at this position eliminates every remaining straddler there. -/
theorem cutBlock_resolves (goLeft : Bool) (cut leftId rightId : ℕ) (block : Frozen)
    (ordered : block.members.Pairwise (outward goLeft)) :
    ∀ piece ∈ cutBlock goLeft cut leftId rightId block, ¬ Straddles cut piece := by
  classical
  unfold cutBlock
  split_ifs with crosses
  · intro piece member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · intro cross
      obtain ⟨first, firstMem, firstLt⟩ := cross.1
      obtain ⟨second, secondMem, secondGe⟩ := cross.2
      have firstInside := List.mem_takeWhile_imp firstMem
      have secondInside := List.mem_takeWhile_imp secondMem
      cases goLeft <;> simp_all [cutPrefix] <;> omega
    · intro cross
      obtain ⟨first, firstMem, firstLt⟩ := cross.1
      obtain ⟨second, secondMem, secondGe⟩ := cross.2
      have firstOutside := dropWhile_cutPrefix_false ordered first firstMem
      have secondOutside := dropWhile_cutPrefix_false ordered second secondMem
      cases goLeft <;> simp_all [cutPrefix] <;> omega
  · simpa using crosses

theorem cutBlock_descends (goLeft : Bool) (cut leftId rightId : ℕ) (block : Frozen) :
    ∀ piece ∈ cutBlock goLeft cut leftId rightId block, Descends piece block := by
  classical
  unfold cutBlock
  split_ifs
  · intro piece member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact ⟨rfl, rfl, List.takeWhile_sublist _⟩
    · exact ⟨rfl, rfl, List.dropWhile_sublist _⟩
  · intro piece member
    have same : piece = block := by simpa using member
    subst piece
    exact descends_refl block

/-- An explicit cut pass. Reserving two names per old block does not
create blocks: homogeneous blocks are retained verbatim. Every actual
split uses its own two reserved fresh logical identifiers. -/
noncomputable def cutList (goLeft : Bool) (cut : ℕ) : ℕ → List Frozen → List Frozen
  | _, [] => []
  | fresh, block :: rest => cutBlock goLeft cut fresh (fresh+1) block ++
      cutList goLeft cut (fresh+2) rest

noncomputable def cutListBirths (cut : ℕ) : List Frozen → ℕ
  | [] => 0
  | block :: rest => cutBlockBirths cut block + cutListBirths cut rest

theorem cutList_entries (goLeft : Bool) (cut fresh : ℕ) (blocks : List Frozen) :
    frozenEntries (cutList goLeft cut fresh blocks) = frozenEntries blocks := by
  induction blocks generalizing fresh with
  | nil => rfl
  | cons block rest ih =>
      change frozenEntries (cutBlock goLeft cut fresh (fresh+1) block ++
        cutList goLeft cut (fresh+2) rest) = block.members ++ frozenEntries rest
      rw [frozenEntries_append, cutBlock_entries, ih]

noncomputable def cutState (goLeft : Bool) (cut fresh : ℕ) (state : SideState) : SideState :=
  ⟨cutList goLeft cut fresh state.shrinking, state.grower⟩

theorem cutState_entries (goLeft : Bool) (cut fresh : ℕ) (state : SideState) :
    entries (cutState goLeft cut fresh state) = entries state := by
  simp only [cutState, entries, cutList_entries]

theorem cutState_valid {owner : ℕ} (goLeft : Bool) (cut fresh : ℕ) (state : SideState)
    (valid : Valid owner goLeft state) : Valid owner goLeft (cutState goLeft cut fresh state) := by
  exact ⟨by simpa only [cutState_entries] using valid.1,
    by simpa only [cutState_entries] using valid.2.1, valid.2.2⟩

theorem cutState_sound {n : ℕ} (snapshot : Snapshot n) (tree : BST 0 n)
    (owner : External n) (goLeft : Bool) (cut fresh : ℕ) (state : SideState)
    (sound : ParentSound snapshot tree owner state) :
    ParentSound snapshot tree owner (cutState goLeft cut fresh state) := by
  simpa only [ParentSound, cutState_entries] using sound

theorem cutList_resolves (goLeft : Bool) (cut fresh : ℕ) (blocks : List Frozen)
    (ordered : (frozenEntries blocks).Pairwise (outward goLeft)) :
    ∀ piece ∈ cutList goLeft cut fresh blocks, ¬ Straddles cut piece := by
  induction blocks generalizing fresh with
  | nil => simp [cutList]
  | cons block rest ih =>
      have ordered' : (block.members ++ frozenEntries rest).Pairwise (outward goLeft) := ordered
      obtain ⟨headOrder, restOrder, _⟩ := List.pairwise_append.mp ordered'
      intro piece member
      rcases List.mem_append.mp member with member | member
      · exact cutBlock_resolves goLeft cut fresh (fresh+1) block headOrder piece member
      · exact ih (fresh+2) restOrder piece member

theorem cutList_descends (goLeft : Bool) (cut fresh : ℕ) (blocks : List Frozen) :
    ∀ piece ∈ cutList goLeft cut fresh blocks,
      ∃ original ∈ blocks, Descends piece original := by
  induction blocks generalizing fresh with
  | nil => simp [cutList]
  | cons block rest ih =>
      intro piece member
      rcases List.mem_append.mp member with member | member
      · exact ⟨block, by simp, cutBlock_descends goLeft cut fresh (fresh+1) block piece member⟩
      · obtain ⟨original, originalMem, history⟩ := ih (fresh+2) piece member
        exact ⟨original, by simp [originalMem], history⟩

theorem cutListBirths_zero (cut : ℕ) (blocks : List Frozen)
    (none : ∀ block ∈ blocks, ¬ Straddles cut block) : cutListBirths cut blocks = 0 := by
  induction blocks with
  | nil => rfl
  | cons block rest ih =>
      have head := none block (by simp)
      have tail : ∀ block ∈ rest, ¬ Straddles cut block := fun block member => none block (by simp [member])
      simp [cutListBirths, cutBlockBirths, head, ih tail]

/-- An entire concrete ordered side incurs at most one binary split at
one cut, hence at most two logical-instance births. -/
theorem cutListBirths_le_two (goLeft : Bool) (cut : ℕ) (blocks : List Frozen)
    (ordered : blocks.Pairwise
      (fun first second => ∀ x ∈ first.members, ∀ y ∈ second.members, outward goLeft x y)) :
    cutListBirths cut blocks ≤ 2 := by
  induction blocks with
  | nil => simp [cutListBirths]
  | cons block rest ih =>
      obtain ⟨headOrder, restOrder⟩ := List.pairwise_cons.mp ordered
      by_cases cross : Straddles cut block
      · have none : ∀ other ∈ rest, ¬ Straddles cut other := by
          intro other member otherCross
          exact straddlers_not_ordered cross otherCross (headOrder other member)
        simp [cutListBirths, cutBlockBirths, cross, cutListBirths_zero cut rest none]
      · simpa [cutListBirths, cutBlockBirths, cross] using ih restOrder

theorem cutState_births_le_two {owner : ℕ} (goLeft : Bool) (cut : ℕ) (state : SideState)
    (valid : Valid owner goLeft state) : cutListBirths cut state.shrinking ≤ 2 :=
  cutListBirths_le_two goLeft cut state.shrinking (ordered_blocks valid)

theorem cutListBirths_side_zero {owner cut : ℕ} {side : Bool} {state : SideState}
    (valid : Valid owner side state) (wrongSide : side ≠ decide (cut ≤ owner)) :
    cutListBirths cut state.shrinking = 0 := by
  apply cutListBirths_zero
  intro block member crosses
  exact wrongSide (straddling_side valid member crosses)

noncomputable def ownerCutBirths {n : ℕ} (states : External n → Bool → SideState)
    (cut : ℕ) (owner : External n) : ℕ :=
  cutListBirths cut (states owner false).shrinking +
    cutListBirths cut (states owner true).shrinking

theorem ownerCutBirths_le_two {n : ℕ} (states : External n → Bool → SideState)
    (cut : ℕ) (owner : External n)
    (valid : ∀ side, Valid owner.val side (states owner side)) :
    ownerCutBirths states cut owner ≤ 2 := by
  unfold ownerCutBirths
  by_cases beforeOwner : cut ≤ owner.val
  · have zero := cutListBirths_side_zero (cut := cut) (valid false) (by simp [beforeOwner])
    rw [zero, zero_add]
    exact cutState_births_le_two true cut _ (valid true)
  · have zero := cutListBirths_side_zero (cut := cut) (valid true) (by simp [beforeOwner])
    rw [zero, add_zero]
    exact cutState_births_le_two false cut _ (valid false)

theorem incidence_ancestor {n depth : ℕ} {before after : BST 0 n}
    (profile : RotationCutProfile before after depth) (tree : BST 0 n)
    {entry : ℕ × ℕ} {owner : External n}
    (member : (entry, owner) ∈ cutOwnerIncidences profile tree) :
    owner ∈ HeapGeometry.Ancestors (Snapshot.ofTree before) tree (border profile entry) := by
  classical
  unfold cutOwnerIncidences at member
  obtain ⟨otherEntry, _, imageMem⟩ := Finset.mem_biUnion.mp member
  obtain ⟨otherOwner, ownerMem, pairEq⟩ := Finset.mem_image.mp imageMem
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj pairEq
  exact ownerMem

/-- If an owner is absent from the actual border's ancestor chain, the
explicit cut algorithm creates zero instances in both its side states. -/
theorem ownerCutBirths_zero_of_unsupported {n depth : ℕ} {before after : BST 0 n}
    (profile : RotationCutProfile before after depth) (tree : BST 0 n)
    (states : External n → Bool → SideState) {entry : ℕ × ℕ}
    (entryMem : entry ∈ profile.entries) (owner : External n)
    (sound : ∀ side, ParentSound (Snapshot.ofTree before) tree owner (states owner side))
    (unsupported : owner ∉ HeapGeometry.Ancestors (Snapshot.ofTree before) tree (border profile entry)) :
    ownerCutBirths states entry.1 owner = 0 := by
  have zero : ∀ side, cutListBirths entry.1 (states owner side).shrinking = 0 := by
    intro side
    apply cutListBirths_zero
    intro block blockMem cross
    apply unsupported
    exact incidence_ancestor profile tree
      (straddling_supported profile tree entryMem (sound side) blockMem cross)
  simp [ownerCutBirths, zero]

noncomputable def allOwnerCutBirths {n : ℕ} (states : External n → Bool → SideState)
    (cut : ℕ) : ℕ := ∑ owner, ownerCutBirths states cut owner

/-- Actual creations of a complete cut pass over all owners are charged
to shallow old-heap ancestors; this remains valid after earlier cut passes
because they preserve the exact flattened entry lists and parent soundness. -/
theorem allOwnerCutBirths_le {n depth : ℕ} {before after : BST 0 n}
    (profile : RotationCutProfile before after depth) (tree : BST 0 n)
    (states : External n → Bool → SideState) {entry : ℕ × ℕ}
    (entryMem : entry ∈ profile.entries)
    (valid : ∀ owner side, Valid owner.val side (states owner side))
    (sound : ∀ owner side, ParentSound (Snapshot.ofTree before) tree owner (states owner side)) :
    allOwnerCutBirths states entry.1 ≤ 2 * (depth+2) := by
  classical
  let ancestors := HeapGeometry.Ancestors (Snapshot.ofTree before) tree (border profile entry)
  have pointwise : ∀ owner, ownerCutBirths states entry.1 owner ≤
      if owner ∈ ancestors then 2 else 0 := by
    intro owner
    by_cases supported : owner ∈ ancestors
    · simpa [supported] using ownerCutBirths_le_two states entry.1 owner (valid owner)
    · rw [if_neg supported]
      exact Nat.le_of_eq (ownerCutBirths_zero_of_unsupported profile tree states entryMem owner
        (sound owner) supported)
  calc
    allOwnerCutBirths states entry.1 ≤ ∑ owner : External n, if owner ∈ ancestors then 2 else 0 :=
      Finset.sum_le_sum fun owner _ => pointwise owner
    _ = 2 * ancestors.card := by simp [Finset.sum_ite_mem, Nat.mul_comm]
    _ ≤ 2 * (depth+2) := by
      apply Nat.mul_le_mul_left
      have size := HeapGeometry.ancestor_card_le_rank_succ (Snapshot.ofTree before) tree
        (border profile entry)
      have shallow := (border_spec profile entry entryMem).2.2
      exact size.trans (by omega)

noncomputable def cutAllOwners {n : ℕ} (cut : ℕ)
    (allocate : External n → Bool → ℕ) (states : External n → Bool → SideState) :
    External n → Bool → SideState :=
  fun owner side => cutState side cut (allocate owner side) (states owner side)

/-- The full deterministic cut sequence, with fresh-name reserves supplied
per stage/owner/side. Its numerical result counts newly born logical
instances, two for each actual nontrivial binary split. -/
noncomputable def prepareCuts {n : ℕ}
    (allocate : ℕ → External n → Bool → ℕ) :
    List (ℕ × ℕ) → ℕ → (External n → Bool → SideState) →
      (External n → Bool → SideState) × ℕ
  | [], _, states => (states, 0)
  | entry :: rest, stage, states =>
      let next := cutAllOwners entry.1 (allocate stage) states
      let tail := prepareCuts allocate rest (stage+1) next
      (tail.1, allOwnerCutBirths states entry.1 + tail.2)

theorem prepareCuts_entries {n : ℕ} (allocate : ℕ → External n → Bool → ℕ)
    (cuts : List (ℕ × ℕ)) (stage : ℕ) (states : External n → Bool → SideState)
    (owner : External n) (side : Bool) :
    entries ((prepareCuts allocate cuts stage states).1 owner side) = entries (states owner side) := by
  induction cuts generalizing stage states with
  | nil => rfl
  | cons entry rest ih =>
      change entries ((prepareCuts allocate rest (stage+1)
        (cutAllOwners entry.1 (allocate stage) states)).1 owner side) = _
      rw [ih]
      exact cutState_entries side entry.1 (allocate stage owner side) (states owner side)

theorem prepareCuts_valid {n : ℕ} (allocate : ℕ → External n → Bool → ℕ)
    (cuts : List (ℕ × ℕ)) (stage : ℕ) (states : External n → Bool → SideState)
    (valid : ∀ owner side, Valid owner.val side (states owner side)) :
    ∀ owner side, Valid owner.val side ((prepareCuts allocate cuts stage states).1 owner side) := by
  induction cuts generalizing stage states with
  | nil => exact valid
  | cons entry rest ih =>
      apply ih
      intro owner side
      exact cutState_valid side entry.1 (allocate stage owner side) _ (valid owner side)

theorem prepareCuts_sound {n : ℕ} (snapshot : Snapshot n) (tree : BST 0 n)
    (allocate : ℕ → External n → Bool → ℕ) (cuts : List (ℕ × ℕ)) (stage : ℕ)
    (states : External n → Bool → SideState)
    (sound : ∀ owner side, ParentSound snapshot tree owner (states owner side)) :
    ∀ owner side, ParentSound snapshot tree owner ((prepareCuts allocate cuts stage states).1 owner side) := by
  intro owner side
  simpa only [ParentSound, prepareCuts_entries] using sound owner side

theorem prepareCuts_births_le {n depth : ℕ} {before after : BST 0 n}
    (profile : RotationCutProfile before after depth) (tree : BST 0 n)
    (allocate : ℕ → External n → Bool → ℕ) (cuts : List (ℕ × ℕ))
    (included : ∀ entry ∈ cuts, entry ∈ profile.entries)
    (stage : ℕ) (states : External n → Bool → SideState)
    (valid : ∀ owner side, Valid owner.val side (states owner side))
    (sound : ∀ owner side, ParentSound (Snapshot.ofTree before) tree owner (states owner side)) :
    (prepareCuts allocate cuts stage states).2 ≤ 2 * (depth+2) * cuts.length := by
  induction cuts generalizing stage states with
  | nil => simp [prepareCuts]
  | cons entry rest ih =>
      have headBound := allOwnerCutBirths_le profile tree states
        (included entry (by simp)) valid sound
      have tailBound := ih (fun other member => included other (by simp [member])) (stage+1)
        (cutAllOwners entry.1 (allocate stage) states)
        (fun owner side => cutState_valid side entry.1 (allocate stage owner side) _ (valid owner side))
        (fun owner side => cutState_sound (Snapshot.ofTree before) tree owner side entry.1
          (allocate stage owner side) _ (sound owner side))
      change allOwnerCutBirths states entry.1 +
        (prepareCuts allocate rest (stage+1) (cutAllOwners entry.1 (allocate stage) states)).2 ≤ _
      simp only [List.length_cons]
      nlinarith

/-- Concrete rank-boundary splitting has a derived quadratic creation
budget; no trace field supplies this inequality. -/
theorem prepareProfile_births_le {n depth : ℕ} {before after : BST 0 n}
    (profile : RotationCutProfile before after depth) (tree : BST 0 n)
    (allocate : ℕ → External n → Bool → ℕ) (stage : ℕ)
    (states : External n → Bool → SideState)
    (valid : ∀ owner side, Valid owner.val side (states owner side))
    (sound : ∀ owner side, ParentSound (Snapshot.ofTree before) tree owner (states owner side)) :
    (prepareCuts allocate profile.entries stage states).2 ≤ 2 * (depth+2)^2 := by
  have bound := prepareCuts_births_le profile tree allocate profile.entries
    (fun _ member => member) stage states valid sound
  have lengthBound := profile.length_le
  nlinarith

theorem prepareCuts_descends {n : ℕ} (allocate : ℕ → External n → Bool → ℕ)
    (cuts : List (ℕ × ℕ)) (stage : ℕ) (states : External n → Bool → SideState)
    (owner : External n) (side : Bool) :
    ∀ piece ∈ ((prepareCuts allocate cuts stage states).1 owner side).shrinking,
      ∃ original ∈ (states owner side).shrinking, Descends piece original := by
  induction cuts generalizing stage states with
  | nil =>
      intro piece member
      exact ⟨piece, member, descends_refl piece⟩
  | cons entry rest ih =>
      intro piece member
      obtain ⟨middle, middleMem, afterMiddle⟩ := ih (stage+1)
        (cutAllOwners entry.1 (allocate stage) states) piece member
      obtain ⟨original, originalMem, middleOriginal⟩ :=
        cutList_descends side entry.1 (allocate stage owner side)
          (states owner side).shrinking middle middleMem
      exact ⟨original, originalMem, descends_trans afterMiddle middleOriginal⟩

theorem descends_not_straddling {cut : ℕ} {after before : Frozen}
    (descendant : Descends after before) (resolved : ¬ Straddles cut before) :
    ¬ Straddles cut after := by
  intro cross
  apply resolved
  obtain ⟨first, firstMem, firstLt⟩ := cross.1
  obtain ⟨second, secondMem, secondGe⟩ := cross.2
  exact ⟨⟨first, descendant.2.2.subset firstMem, firstLt⟩,
    ⟨second, descendant.2.2.subset secondMem, secondGe⟩⟩

theorem prepareCuts_resolves {n : ℕ} (allocate : ℕ → External n → Bool → ℕ)
    (cuts : List (ℕ × ℕ)) (stage : ℕ) (states : External n → Bool → SideState)
    (valid : ∀ owner side, Valid owner.val side (states owner side))
    (owner : External n) (side : Bool) :
    ∀ entry ∈ cuts, ∀ piece ∈ ((prepareCuts allocate cuts stage states).1 owner side).shrinking,
      ¬ Straddles entry.1 piece := by
  induction cuts generalizing stage states with
  | nil => simp
  | cons first rest ih =>
      intro entry entryMem piece pieceMem
      rcases List.mem_cons.mp entryMem with rfl | entryMem
      · obtain ⟨middle, middleMem, descendant⟩ := prepareCuts_descends allocate rest (stage+1)
          (cutAllOwners entry.1 (allocate stage) states) owner side piece pieceMem
        apply descends_not_straddling descendant
        exact cutList_resolves side entry.1 (allocate stage owner side) (states owner side).shrinking
          (List.pairwise_append.mp (valid owner side).1).1 middle middleMem
      · exact ih (stage+1) (cutAllOwners first.1 (allocate stage) states)
          (fun owner side => cutState_valid side first.1 (allocate stage owner side) _ (valid owner side))
          entry entryMem piece pieceMem

/-- Every output shrinking block has one actual comparator-depth shift,
so the numerical offset transport applies uniformly to all its members. -/
theorem prepareProfile_uniform_shift {n depth : ℕ} {before after : BST 0 n}
    (profile : RotationCutProfile before after depth)
    (allocate : ℕ → External n → Bool → ℕ) (stage : ℕ)
    (states : External n → Bool → SideState)
    (valid : ∀ owner side, Valid owner.val side (states owner side))
    (owner : External n) (side : Bool) {piece : Frozen}
    (pieceMem : piece ∈ ((prepareCuts allocate profile.entries stage states).1 owner side).shrinking)
    {first second : Entry} (firstMem : first ∈ piece.members) (secondMem : second ∈ piece.members) :
    (after.externalDepth first.key : ℤ) - before.externalDepth first.key =
      (after.externalDepth second.key : ℤ) - before.externalDepth second.key := by
  apply profile.uniform
  intro entry entryMem
  have resolved := prepareCuts_resolves allocate profile.entries stage states valid owner side
    entry entryMem piece pieceMem
  constructor
  · intro firstBefore
    by_contra secondNotBefore
    exact resolved ⟨⟨first, firstMem, firstBefore⟩, ⟨second, secondMem, by omega⟩⟩
  · intro secondBefore
    by_contra firstNotBefore
    exact resolved ⟨⟨second, secondMem, secondBefore⟩, ⟨first, firstMem, by omega⟩⟩

#print axioms straddling_index_unique
#print axioms straddling_side
#print axioms straddling_supported
#print axioms straddling_occurrences_card
#print axioms cutBlock_resolves
#print axioms cutBlock_descends
#print axioms cutState_valid
#print axioms cutList_resolves
#print axioms cutState_births_le_two
#print axioms allOwnerCutBirths_le
#print axioms prepareProfile_births_le
#print axioms prepareProfile_uniform_shift
#print axioms prepareCuts_descends

end GreedyMerge.OrderedBlocks

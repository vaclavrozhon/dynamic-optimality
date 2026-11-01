import Splay.Interface.Activity
import Mathlib.Data.Finset.SDiff

namespace Splay.Interface

open Finset

/--
The elements carried by all blocks of one ghost lineage.

The recursion deliberately consumes the block list and the parallel root-label
list together.  On aligned states no entry is dropped; keeping the definition
total makes it usable without bundled alignment proofs.
-/
def lineageElementsOf {n : ℕ} :
    List (Block n) → RootLabels → RootId → Finset (Element n)
  | block :: blocks, label :: labels, root =>
      (if label = root then block.elements.toFinset else ∅) ∪
        lineageElementsOf blocks labels root
  | _, _, _ => ∅

/-- The payload of one lineage in an aligned state/label snapshot. -/
def lineageElements {n : ℕ} (state : State n) (labels : RootLabels)
    (root : RootId) : Finset (Element n) :=
  lineageElementsOf state.blocks labels root

@[simp]
theorem lineageElementsOf_nil_left {n : ℕ} (labels : RootLabels)
    (root : RootId) :
    lineageElementsOf ([] : List (Block n)) labels root = ∅ :=
  rfl

@[simp]
theorem lineageElementsOf_nil_right {n : ℕ} (blocks : List (Block n))
    (root : RootId) :
    lineageElementsOf blocks [] root = ∅ := by
  cases blocks <;> rfl

@[simp]
theorem lineageElementsOf_cons {n : ℕ} (block : Block n)
    (blocks : List (Block n)) (label : RootId) (labels : RootLabels)
    (root : RootId) :
    lineageElementsOf (block :: blocks) (label :: labels) root =
      (if label = root then block.elements.toFinset else ∅) ∪
        lineageElementsOf blocks labels root :=
  rfl

/-- Every payload element is an element of the underlying block collection. -/
theorem mem_flatMap_elements_of_mem_lineageElementsOf
    {n : ℕ} {blocks : List (Block n)} {labels : RootLabels}
    {root : RootId} {element : Element n}
    (member : element ∈ lineageElementsOf blocks labels root) :
    element ∈ blocks.flatMap Block.elements := by
  induction blocks generalizing labels with
  | nil =>
      simp at member
  | cons block blocks ih =>
      cases labels with
      | nil =>
          simp at member
      | cons label labels =>
          simp only [lineageElementsOf_cons, Finset.mem_union] at member
          simp only [List.flatMap_cons, List.mem_append]
          rcases member with head | tail
          · left
            split at head
            · simpa using head
            · simp at head
          · exact Or.inr (ih tail)

/-- A successful block lookup embeds all of that block's elements globally. -/
theorem mem_flatMap_elements_of_getElem?
    {n : ℕ} {blocks : List (Block n)} {blockId : BlockId}
    {block : Block n} {element : Element n}
    (found : blocks[blockId]? = some block)
    (member : element ∈ block.elements) :
    element ∈ blocks.flatMap Block.elements := by
  have block_mem : block ∈ blocks :=
    List.mem_of_getElem? found
  exact List.mem_flatMap.mpr ⟨block, block_mem, member⟩

/--
Lookup characterization of lineage membership.  This is the extensional API
used by later trace arguments; it is independent of block order.
-/
theorem mem_lineageElementsOf_iff
    {n : ℕ} {blocks : List (Block n)} {labels : RootLabels}
    {root : RootId} {element : Element n}
    (aligned : labels.length = blocks.length) :
    element ∈ lineageElementsOf blocks labels root ↔
      ∃ (blockId : BlockId) (block : Block n),
        blocks[blockId]? = some block ∧
          labels[blockId]? = some root ∧
          element ∈ block.elements := by
  induction blocks generalizing labels with
  | nil =>
      have labels_nil : labels = [] := by
        simpa using aligned
      subst labels
      simp
  | cons block blocks ih =>
      cases labels with
      | nil =>
          simp at aligned
      | cons label labels =>
          have tail_aligned : labels.length = blocks.length := by
            simpa using aligned
          constructor
          · intro member
            simp only [lineageElementsOf_cons, Finset.mem_union] at member
            rcases member with head | tail
            · have label_eq : label = root := by
                by_contra label_ne
                simp [label_ne] at head
              have element_mem : element ∈ block.elements := by
                simpa [label_eq] using head
              exact ⟨0, block, rfl, by simp [label_eq], element_mem⟩
            · obtain ⟨blockId, tailBlock, block_found, root_found,
                  element_mem⟩ :=
                (ih tail_aligned).mp tail
              exact
                ⟨Nat.succ blockId, tailBlock, by simpa using block_found,
                  by simpa using root_found, element_mem⟩
          · rintro ⟨blockId, foundBlock, block_found, root_found,
                element_mem⟩
            cases blockId with
            | zero =>
                simp only [List.getElem?_cons_zero, Option.some.injEq] at block_found root_found
                subst foundBlock
                subst label
                simp [element_mem]
            | succ blockId =>
                apply Finset.mem_union_right
                apply (ih tail_aligned).mpr
                exact
                  ⟨blockId, foundBlock, by simpa using block_found,
                    by simpa using root_found, element_mem⟩

@[simp]
theorem mem_lineageElements_iff
    {n : ℕ} {state : State n} {labels : RootLabels}
    {root : RootId} {element : Element n}
    (aligned : labels.length = state.blocks.length) :
    element ∈ lineageElements state labels root ↔
      ∃ (blockId : BlockId) (block : Block n),
        state.block? blockId = some block ∧
          RootLabels.root? labels blockId = some root ∧
          element ∈ block.elements := by
  simpa [lineageElements, State.block?, RootLabels.root?] using
    (mem_lineageElementsOf_iff
      (blocks := state.blocks) (labels := labels)
      (root := root) (element := element) aligned)

/-- Every element of a labelled block belongs to that lineage's payload. -/
theorem block_elements_subset_lineageElementsOf
    {n : ℕ} {blocks : List (Block n)} {labels : RootLabels}
    (aligned : labels.length = blocks.length)
    {blockId : BlockId} {block : Block n} {root : RootId}
    (block_found : blocks[blockId]? = some block)
    (root_found : labels[blockId]? = some root) :
    block.elements.toFinset ⊆ lineageElementsOf blocks labels root := by
  intro element element_mem
  apply (mem_lineageElementsOf_iff aligned).mpr
  exact
    ⟨blockId, block, block_found, root_found, by simpa using element_mem⟩

/-- Payloads distribute over appending aligned block/label suffixes. -/
theorem lineageElementsOf_append
    {n : ℕ} {blocks : List (Block n)} {labels : RootLabels}
    (aligned : labels.length = blocks.length)
    (moreBlocks : List (Block n)) (moreLabels : RootLabels)
    (root : RootId) :
    lineageElementsOf (blocks ++ moreBlocks) (labels ++ moreLabels) root =
      lineageElementsOf blocks labels root ∪
        lineageElementsOf moreBlocks moreLabels root := by
  induction blocks generalizing labels with
  | nil =>
      have labels_nil : labels = [] := by
        simpa using aligned
      subst labels
      simp
  | cons block blocks ih =>
      cases labels with
      | nil =>
          simp at aligned
      | cons label labels =>
          have tail_aligned : labels.length = blocks.length := by
            simpa using aligned
          simp only [List.cons_append, lineageElementsOf_cons]
          rw [ih tail_aligned]
          simp only [Finset.union_assoc]

/--
Changing block metadata while preserving every block's element list preserves
all lineage payloads.
-/
theorem lineageElementsOf_modify_elements_eq
    {n : ℕ} {blocks : List (Block n)} {labels : RootLabels}
    (aligned : labels.length = blocks.length)
    (blockId : BlockId) (update : Block n → Block n)
    (elements_eq : ∀ block, (update block).elements = block.elements)
    (root : RootId) :
    lineageElementsOf (blocks.modify blockId update) labels root =
      lineageElementsOf blocks labels root := by
  induction blocks generalizing labels blockId with
  | nil =>
      simp
  | cons block blocks ih =>
      cases labels with
      | nil =>
          simp
      | cons label labels =>
          have tail_aligned : labels.length = blocks.length := by
            simpa using aligned
          cases blockId with
          | zero =>
              simp [lineageElementsOf, elements_eq]
          | succ blockId =>
              simp only [List.modify_succ_cons, lineageElementsOf_cons]
              rw [ih tail_aligned blockId]

/-- Prepending at one block adds exactly one element to its labelled lineage. -/
theorem lineageElementsOf_modify_cons
    {n : ℕ} {blocks : List (Block n)} {labels : RootLabels}
    (aligned : labels.length = blocks.length)
    (blockId : BlockId) (element : Element n) (root : RootId) :
    lineageElementsOf
        (blocks.modify blockId fun block =>
          { block with elements := element :: block.elements })
        labels root =
      lineageElementsOf blocks labels root ∪
        if labels[blockId]? = some root then {element} else ∅ := by
  induction blocks generalizing labels blockId with
  | nil =>
      have labels_nil : labels = [] := by
        simpa using aligned
      subst labels
      simp
  | cons block blocks ih =>
      cases labels with
      | nil =>
          simp at aligned
      | cons label labels =>
          have tail_aligned : labels.length = blocks.length := by
            simpa using aligned
          cases blockId with
          | zero =>
              by_cases label_eq : label = root
              · simp [lineageElementsOf, label_eq,
                  Finset.union_comm, Finset.union_left_comm]
              · simp [lineageElementsOf, label_eq]
          | succ blockId =>
              simp only [List.modify_succ_cons, lineageElementsOf_cons,
                List.getElem?_cons_succ]
              rw [ih tail_aligned blockId]
              simp only [Finset.union_assoc]
              rfl

/--
Erasing an element from its unique owning block removes it from exactly that
block's labelled lineage.
-/
theorem lineageElementsOf_modify_erase
    {n : ℕ} {blocks : List (Block n)} {labels : RootLabels}
    (aligned : labels.length = blocks.length)
    (nodup : (blocks.flatMap Block.elements).Nodup)
    (blockId : BlockId) {block : Block n} (element : Element n)
    (found : blocks[blockId]? = some block)
    (present : element ∈ block.elements)
    (root : RootId) :
    lineageElementsOf
        (blocks.modify blockId fun current =>
          { current with elements := current.elements.erase element })
        labels root =
      lineageElementsOf blocks labels root \
        if labels[blockId]? = some root then {element} else ∅ := by
  induction blocks generalizing labels blockId block with
  | nil =>
      simp at found
  | cons head blocks ih =>
      cases labels with
      | nil =>
          simp at aligned
      | cons label labels =>
          have tail_aligned : labels.length = blocks.length := by
            simpa using aligned
          have split_nodup :
              head.elements.Nodup ∧
                (blocks.flatMap Block.elements).Nodup ∧
                ∀ a ∈ head.elements, ∀ b ∈ blocks.flatMap Block.elements,
                  a ≠ b := by
            change
              (head.elements ++ blocks.flatMap Block.elements).Nodup at nodup
            exact List.nodup_append.mp nodup
          cases blockId with
          | zero =>
              simp only [List.getElem?_cons_zero, Option.some.injEq] at found
              subst block
              by_cases label_eq : label = root
              · have element_not_tail :
                    element ∉ lineageElementsOf blocks labels root := by
                  intro tail_member
                  have tail_global :=
                    mem_flatMap_elements_of_mem_lineageElementsOf tail_member
                  exact
                    split_nodup.2.2 element present element tail_global rfl
                ext current
                by_cases current_eq : current = element
                · subst current
                  simp [lineageElementsOf, label_eq, present,
                    element_not_tail, split_nodup.1.not_mem_erase]
                · simp [lineageElementsOf, label_eq, current_eq]
              · simp [lineageElementsOf, label_eq]
          | succ blockId =>
              have tail_found : blocks[blockId]? = some block := by
                simpa using found
              have element_tail :
                  element ∈ blocks.flatMap Block.elements :=
                mem_flatMap_elements_of_getElem? tail_found present
              have element_not_head : element ∉ head.elements := by
                intro head_member
                exact
                  split_nodup.2.2 element head_member element element_tail
                    rfl
              have tail_eq :=
                ih tail_aligned split_nodup.2.1 blockId tail_found present
              simp only [List.modify_succ_cons, lineageElementsOf_cons,
                List.getElem?_cons_succ]
              rw [tail_eq]
              ext current
              simp only [Finset.mem_union, Finset.mem_sdiff]
              have head_safe :
                  current ∈
                      (if label = root then head.elements.toFinset else ∅) →
                    current ∉
                      (if labels[blockId]? = some root then
                        ({element} : Finset (Element n))
                      else (∅ : Finset (Element n))) := by
                intro current_head current_removed
                have current_mem_head : current ∈ head.elements := by
                  by_cases label_eq : label = root
                  · simpa [label_eq] using current_head
                  · simp [label_eq] at current_head
                have current_eq : current = element := by
                  by_cases root_eq : labels[blockId]? = some root
                  · simpa [root_eq] using current_removed
                  · simp [root_eq] at current_removed
                subst current
                exact element_not_head current_mem_head
              constructor
              · rintro (current_head | ⟨current_tail, current_safe⟩)
                · exact ⟨Or.inl current_head, head_safe current_head⟩
                · exact ⟨Or.inr current_tail, current_safe⟩
              · rintro ⟨current_head | current_tail, current_safe⟩
                · exact Or.inl current_head
                · exact Or.inr ⟨current_tail, current_safe⟩

/--
General form of unique-owner removal: replacing one block's element set by a
set difference removes precisely that difference from the block's lineage.
-/
theorem lineageElementsOf_modify_sdiff
    {n : ℕ} {blocks : List (Block n)} {labels : RootLabels}
    (aligned : labels.length = blocks.length)
    (nodup : (blocks.flatMap Block.elements).Nodup)
    (blockId : BlockId) {block : Block n}
    (found : blocks[blockId]? = some block)
    (removed : Finset (Element n))
    (removed_subset : removed ⊆ block.elements.toFinset)
    (update : Block n → Block n)
    (updated_elements :
      (update block).elements.toFinset =
        block.elements.toFinset \ removed)
    (root : RootId) :
    lineageElementsOf (blocks.modify blockId update) labels root =
      lineageElementsOf blocks labels root \
        if labels[blockId]? = some root then removed else ∅ := by
  induction blocks generalizing labels blockId block with
  | nil =>
      simp at found
  | cons head blocks ih =>
      cases labels with
      | nil =>
          simp at aligned
      | cons label labels =>
          have tail_aligned : labels.length = blocks.length := by
            simpa using aligned
          have split_nodup :
              head.elements.Nodup ∧
                (blocks.flatMap Block.elements).Nodup ∧
                ∀ a ∈ head.elements, ∀ b ∈ blocks.flatMap Block.elements,
                  a ≠ b := by
            change
              (head.elements ++ blocks.flatMap Block.elements).Nodup at nodup
            exact List.nodup_append.mp nodup
          cases blockId with
          | zero =>
              simp only [List.getElem?_cons_zero, Option.some.injEq] at found
              subst block
              by_cases label_eq : label = root
              · subst label
                simp only [List.modify_cons, if_pos, lineageElementsOf_cons,
                  List.getElem?_cons_zero]
                change
                  (update head).elements.toFinset ∪
                      lineageElementsOf blocks labels root =
                    (head.elements.toFinset ∪
                        lineageElementsOf blocks labels root) \
                      removed
                rw [updated_elements]
                ext current
                simp only [Finset.mem_union, Finset.mem_sdiff]
                have tail_safe :
                    current ∈ lineageElementsOf blocks labels root →
                      current ∉ removed := by
                  intro current_tail current_removed
                  have current_head : current ∈ head.elements := by
                    simpa using removed_subset current_removed
                  have current_tail_global :=
                    mem_flatMap_elements_of_mem_lineageElementsOf current_tail
                  exact
                    split_nodup.2.2 current current_head current
                      current_tail_global rfl
                constructor
                · rintro (⟨current_head, current_safe⟩ | current_tail)
                  · exact ⟨Or.inl current_head, current_safe⟩
                  · exact ⟨Or.inr current_tail, tail_safe current_tail⟩
                · rintro ⟨current_head | current_tail, current_safe⟩
                  · exact Or.inl ⟨current_head, current_safe⟩
                  · exact Or.inr current_tail
              · simp [lineageElementsOf, label_eq]
          | succ blockId =>
              have tail_found : blocks[blockId]? = some block := by
                simpa using found
              have removed_tail :
                  ∀ ⦃current⦄, current ∈ removed →
                    current ∈ blocks.flatMap Block.elements := by
                intro current current_removed
                exact
                  mem_flatMap_elements_of_getElem? tail_found
                    (by simpa using removed_subset current_removed)
              have head_safe :
                  ∀ ⦃current⦄, current ∈ head.elements →
                    current ∉ removed := by
                intro current current_head current_removed
                exact
                  split_nodup.2.2 current current_head current
                    (removed_tail current_removed) rfl
              have tail_eq :=
                ih tail_aligned split_nodup.2.1 blockId tail_found
                  removed_subset updated_elements
              simp only [List.modify_succ_cons, lineageElementsOf_cons,
                List.getElem?_cons_succ]
              rw [tail_eq]
              ext current
              simp only [Finset.mem_union, Finset.mem_sdiff]
              have head_payload_safe :
                  current ∈
                      (if label = root then head.elements.toFinset else ∅) →
                    current ∉
                      (if labels[blockId]? = some root then removed else ∅) := by
                intro current_head current_removed
                have current_mem_head : current ∈ head.elements := by
                  by_cases label_eq : label = root
                  · simpa [label_eq] using current_head
                  · simp [label_eq] at current_head
                have current_mem_removed : current ∈ removed := by
                  by_cases root_eq : labels[blockId]? = some root
                  · simpa [root_eq] using current_removed
                  · simp [root_eq] at current_removed
                exact head_safe current_mem_head current_mem_removed
              constructor
              · rintro (current_head | ⟨current_tail, current_safe⟩)
                · exact
                    ⟨Or.inl current_head, head_payload_safe current_head⟩
                · exact ⟨Or.inr current_tail, current_safe⟩
              · rintro ⟨current_head | current_tail, current_safe⟩
                · exact Or.inl current_head
                · exact Or.inr ⟨current_tail, current_safe⟩

/-- The losers delivered by a pass to blocks carrying a fixed root label. -/
def destinationLineageLosers {n : ℕ} (labels : RootLabels) :
    List (Pairing n) → RootId → Finset (Element n)
  | [], _ => ∅
  | pairing :: matching, root =>
      (if labels[pairing.destination]? = some root then
        {pairing.loser}
      else ∅) ∪
        destinationLineageLosers labels matching root

/-- The source removals charged to a fixed lineage in one pass. -/
def sourceLineageLosers {n : ℕ} (labels : RootLabels)
    (sourceId : BlockId) (matching : List (Pairing n))
    (root : RootId) : Finset (Element n) :=
  if labels[sourceId]? = some root then
    (pairingLosers matching).toFinset
  else ∅

@[simp]
theorem destinationLineageLosers_nil {n : ℕ} (labels : RootLabels)
    (root : RootId) :
    destinationLineageLosers labels ([] : List (Pairing n)) root = ∅ :=
  rfl

@[simp]
theorem destinationLineageLosers_cons {n : ℕ} (labels : RootLabels)
    (pairing : Pairing n) (matching : List (Pairing n))
    (root : RootId) :
    destinationLineageLosers labels (pairing :: matching) root =
      (if labels[pairing.destination]? = some root then
        {pairing.loser}
      else ∅) ∪ destinationLineageLosers labels matching root :=
  rfl

@[simp]
theorem mem_destinationLineageLosers_iff
    {n : ℕ} {labels : RootLabels} {matching : List (Pairing n)}
    {root : RootId} {element : Element n} :
    element ∈ destinationLineageLosers labels matching root ↔
      ∃ pairing ∈ matching,
        pairing.loser = element ∧
          labels[pairing.destination]? = some root := by
  induction matching with
  | nil =>
      simp
  | cons pairing matching ih =>
      by_cases destination_root :
          labels[pairing.destination]? = some root
      · simp [destinationLineageLosers, destination_root, ih, eq_comm]
      · simp [destinationLineageLosers, destination_root, ih]

/-!
The next two lemmas expose the exact set semantics of repeated list erasure.
The `Nodup` assumption is essential: `List.erase` removes one occurrence,
whereas the payload is a `Finset`.
-/
theorem toFinset_foldl_erase
    {α : Type*} [DecidableEq α]
    (elements removals : List α) (nodup : elements.Nodup) :
    (removals.foldl
        (fun remaining element => remaining.erase element)
        elements).toFinset =
      elements.toFinset \ removals.toFinset := by
  induction removals generalizing elements with
  | nil =>
      simp
  | cons removal removals ih =>
      simp only [List.foldl_cons]
      rw [ih (elements := elements.erase removal) (nodup.erase removal)]
      ext current
      simp only [Finset.mem_sdiff, List.mem_toFinset]
      rw [nodup.mem_erase_iff]
      simp only [List.mem_cons, not_or]
      aesop

/-- `removeLosers` is exactly source-set difference by all matching losers. -/
theorem removeLosers_toFinset
    {n : ℕ} (elements : List (Element n))
    (matching : List (Pairing n)) (nodup : elements.Nodup) :
    (removeLosers elements matching).toFinset =
      elements.toFinset \ (pairingLosers matching).toFinset := by
  rw [removeLosers_eq_foldl]
  exact toFinset_foldl_erase elements (pairingLosers matching) nodup

/-- Taking and dropping at the same cut partitions a list's underlying set. -/
theorem toFinset_take_union_drop
    {α : Type*} [DecidableEq α] (elements : List α) (cut : ℕ) :
    (elements.take cut).toFinset ∪ (elements.drop cut).toFinset =
      elements.toFinset := by
  ext element
  simp only [Finset.mem_union, List.mem_toFinset]
  constructor
  · intro member
    have appended :
        element ∈ elements.take cut ++ elements.drop cut :=
      List.mem_append.mpr member
    simpa only [List.take_append_drop] using appended
  · intro member
    have appended :
        element ∈ elements.take cut ++ elements.drop cut := by
      simpa only [List.take_append_drop] using member
    exact List.mem_append.mp appended

/-- Valid matching losers are a subset of the pre-pass source payload. -/
theorem MatchingValid.pairingLosers_subset
    {n : ℕ} {params : Parameters} {state : State n}
    {sourceId : BlockId} {source : Block n}
    {matching : List (Pairing n)}
    (valid : MatchingValid params state sourceId source matching) :
    (pairingLosers matching).toFinset ⊆ source.elements.toFinset := by
  intro element element_mem
  obtain ⟨pairing, pairing_mem, loser_eq⟩ :=
    List.mem_map.mp (by simpa [pairingLosers] using element_mem)
  subst element
  simpa using valid.loser_mem pairing_mem

/-- Every block of a globally valid state has a duplicate-free element list. -/
theorem State.Valid.block_elements_nodup
    {n : ℕ} {params : Parameters} {state : State n}
    (valid : state.Valid params) {blockId : BlockId} {block : Block n}
    (found : state.block? blockId = some block) :
    block.elements.Nodup := by
  have block_mem : block ∈ state.blocks := by
    exact List.mem_of_getElem? found
  exact (List.nodup_flatMap.mp valid.1).1 block block_mem

/--
Folding destination insertions adds exactly the losers whose destination
blocks carry the queried root label.
-/
theorem lineageElementsOf_insertAtDestinations
    {n : ℕ} {blocks : List (Block n)} {labels : RootLabels}
    (aligned : labels.length = blocks.length)
    (matching : List (Pairing n)) (root : RootId) :
    lineageElementsOf (insertAtDestinations blocks matching) labels root =
      lineageElementsOf blocks labels root ∪
        destinationLineageLosers labels matching root := by
  induction matching generalizing blocks with
  | nil =>
      simp [insertAtDestinations]
  | cons pairing matching ih =>
      change
        lineageElementsOf
            (insertAtDestinations
              (blocks.modify pairing.destination fun destination =>
                { destination with
                  elements := pairing.loser :: destination.elements })
              matching)
            labels root =
          lineageElementsOf blocks labels root ∪
            destinationLineageLosers labels (pairing :: matching) root
      rw [ih (by simpa using aligned)]
      rw [lineageElementsOf_modify_cons aligned]
      simp only [destinationLineageLosers_cons, Finset.union_assoc]

/-- Destination filtering preserves the exact number of selected losers. -/
theorem card_destinationLineageLosers
    {n : ℕ} {labels : RootLabels} {matching : List (Pairing n)}
    (losers_nodup : (pairingLosers matching).Nodup)
    (root : RootId) :
    (destinationLineageLosers labels matching root).card =
      (matching.filter fun pairing =>
        decide (labels[pairing.destination]? = some root)).length := by
  induction matching with
  | nil =>
      simp
  | cons pairing matching ih =>
      have head_not_tail :
          pairing.loser ∉ pairingLosers matching := by
        simpa [pairingLosers] using
          (List.nodup_cons.mp losers_nodup).1
      have tail_nodup : (pairingLosers matching).Nodup := by
        simpa [pairingLosers] using
          (List.nodup_cons.mp losers_nodup).2
      have head_not_destination :
          pairing.loser ∉
            destinationLineageLosers labels matching root := by
        intro member
        obtain ⟨later, later_mem, loser_eq, _destination_root⟩ :=
          mem_destinationLineageLosers_iff.mp member
        apply head_not_tail
        exact List.mem_map.mpr ⟨later, later_mem, loser_eq⟩
      by_cases destination_root :
          labels[pairing.destination]? = some root
      · simp [destinationLineageLosers, destination_root,
          head_not_destination, ih tail_nodup]
      · simp [destinationLineageLosers, destination_root,
          ih tail_nodup]

/-- At its actual source root, a valid pass removes one distinct loser per pairing. -/
theorem MatchingValid.card_sourceLineageLosers
    {n : ℕ} {params : Parameters} {state : State n}
    {sourceId : BlockId} {source : Block n}
    {matching : List (Pairing n)}
    (valid : MatchingValid params state sourceId source matching)
    {labels : RootLabels} {root : RootId}
    (root_found : RootLabels.root? labels sourceId = some root) :
    (sourceLineageLosers labels sourceId matching root).card =
      matching.length := by
  have losers_nodup : (pairingLosers matching).Nodup :=
    pairingLosers_nodup valid.2.1
  simp [sourceLineageLosers, RootLabels.root?] at root_found ⊢
  rw [root_found]
  simpa [pairingLosers] using
    List.toFinset_card_of_nodup losers_nodup

/-- Cardinality of a lineage payload. -/
def lineageSize {n : ℕ} (state : State n) (labels : RootLabels)
    (root : RootId) : ℕ :=
  (lineageElements state labels root).card

namespace HistoryStep

/-- Conversion changes only mode metadata, so every lineage payload is fixed. -/
theorem lineageElements_convert
    {n : ℕ} {params : Parameters}
    {before after : State n} {beforeLabels afterLabels : RootLabels}
    {blockId : BlockId}
    (historyStep :
      HistoryStep params before beforeLabels (.convert blockId)
        after afterLabels)
    (aligned : beforeLabels.length = before.blocks.length)
    (root : RootId) :
    lineageElements after afterLabels root =
      lineageElements before beforeLabels root := by
  rcases historyStep with ⟨step, labels_eq⟩
  rw [labels_eq]
  rcases step with ⟨_before_valid, effect, _after_valid⟩
  cases effect with
  | convert found growing blocks_eq values_eq =>
      simp only [RootLabels.after]
      unfold lineageElements
      rw [blocks_eq]
      apply lineageElementsOf_modify_elements_eq aligned
      intro current
      rfl

/--
Creation appends an empty, freshly labelled block and leaves every existing
(and every other queried) lineage payload unchanged.
-/
theorem lineageElements_create
    {n : ℕ} {params : Parameters}
    {before after : State n} {beforeLabels afterLabels : RootLabels}
    {creator : Element n}
    (historyStep :
      HistoryStep params before beforeLabels (.create creator)
        after afterLabels)
    (aligned : beforeLabels.length = before.blocks.length)
    (root : RootId) :
    lineageElements after afterLabels root =
      lineageElements before beforeLabels root := by
  rcases historyStep with ⟨step, labels_eq⟩
  rw [labels_eq]
  rcases step with ⟨_before_valid, effect, _after_valid⟩
  cases effect with
  | create room blocks_eq values_eq =>
      unfold lineageElements
      rw [blocks_eq, RootLabels.after_create]
      rw [lineageElementsOf_append aligned]
      simp

/-- Insert adds exactly one element to the target block's lineage. -/
theorem lineageElements_insert
    {n : ℕ} {params : Parameters}
    {before after : State n} {beforeLabels afterLabels : RootLabels}
    {blockId : BlockId} {element : Element n}
    (historyStep :
      HistoryStep params before beforeLabels (.insert blockId element)
        after afterLabels)
    (aligned : beforeLabels.length = before.blocks.length)
    (root : RootId) :
    lineageElements after afterLabels root =
      lineageElements before beforeLabels root ∪
        if RootLabels.root? beforeLabels blockId = some root then
          {element}
        else ∅ := by
  rcases historyStep with ⟨step, labels_eq⟩
  rw [labels_eq]
  rcases step with ⟨_before_valid, effect, _after_valid⟩
  cases effect with
  | insert found growing unassigned value_order blocks_eq values_eq =>
      simp only [RootLabels.after]
      unfold lineageElements
      rw [blocks_eq]
      unfold RootLabels.root?
      convert
        lineageElementsOf_modify_cons aligned blockId element root using 1

/-- Delete removes exactly one element from the source block's lineage. -/
theorem lineageElements_delete
    {n : ℕ} {params : Parameters}
    {before after : State n} {beforeLabels afterLabels : RootLabels}
    {blockId : BlockId} {element : Element n}
    (historyStep :
      HistoryStep params before beforeLabels (.delete blockId element)
        after afterLabels)
    (aligned : beforeLabels.length = before.blocks.length)
    (root : RootId) :
    lineageElements after afterLabels root =
      lineageElements before beforeLabels root \
        if RootLabels.root? beforeLabels blockId = some root then
          {element}
        else ∅ := by
  rcases historyStep with ⟨step, labels_eq⟩
  rw [labels_eq]
  rcases step with ⟨before_valid, effect, _after_valid⟩
  cases effect with
  | delete found shrinking present blocks_eq values_eq =>
      simp only [RootLabels.after]
      unfold lineageElements
      rw [blocks_eq]
      apply lineageElementsOf_modify_erase aligned before_valid.1
        blockId element
      · exact found
      · exact present

/--
A pass removes all losers from the source lineage and adds each loser to the
lineage of its actual destination block.  Source and destination lineages are
allowed to coincide; the set formula remains exact in that case.
-/
theorem lineageElements_pass
    {n : ℕ} {params : Parameters}
    {before after : State n} {beforeLabels afterLabels : RootLabels}
    {blockId : BlockId} {matching : List (Pairing n)}
    (historyStep :
      HistoryStep params before beforeLabels (.pass blockId matching)
        after afterLabels)
    (aligned : beforeLabels.length = before.blocks.length)
    (root : RootId) :
    lineageElements after afterLabels root =
      (lineageElements before beforeLabels root \
          sourceLineageLosers beforeLabels blockId matching root) ∪
        destinationLineageLosers beforeLabels matching root := by
  rcases historyStep with ⟨step, labels_eq⟩
  rw [labels_eq]
  rcases step with ⟨before_valid, effect, _after_valid⟩
  cases effect with
  | pass found valid_matching blocks_eq values_eq =>
      rename_i source
      simp only [RootLabels.after]
      have global_nodup :
          (before.blocks.flatMap Block.elements).Nodup := by
        simpa [State.allElements] using before_valid.1
      have source_nodup : source.elements.Nodup :=
        before_valid.block_elements_nodup found
      have removed_subset :
          (pairingLosers matching).toFinset ⊆
            source.elements.toFinset :=
        valid_matching.pairingLosers_subset
      have updated_elements :
          (removeLosers source.elements matching).toFinset =
            source.elements.toFinset \
              (pairingLosers matching).toFinset :=
        removeLosers_toFinset source.elements matching source_nodup
      unfold lineageElements
      rw [blocks_eq]
      change
        lineageElementsOf
            (insertAtDestinations
              (before.blocks.modify blockId fun _ =>
                { source with
                  passCount := source.passCount + 1
                  elements := removeLosers source.elements matching })
              matching)
            beforeLabels root =
          (lineageElementsOf before.blocks beforeLabels root \
              sourceLineageLosers beforeLabels blockId matching root) ∪
            destinationLineageLosers beforeLabels matching root
      rw [lineageElementsOf_insertAtDestinations
        (by simpa using aligned)]
      have source_update :=
        lineageElementsOf_modify_sdiff aligned global_nodup blockId
          found (pairingLosers matching).toFinset removed_subset
          (fun _ =>
            { source with
              passCount := source.passCount + 1
              elements := removeLosers source.elements matching })
          updated_elements root
      rw [source_update]
      rfl

/--
Split only repartitions the source payload between two fresh descendants of
the same root; the union carried by every lineage is unchanged.
-/
theorem lineageElements_split
    {n : ℕ} {params : Parameters}
    {before after : State n} {beforeLabels afterLabels : RootLabels}
    {blockId prefixLength : BlockId}
    (historyStep :
      HistoryStep params before beforeLabels
        (.split blockId prefixLength) after afterLabels)
    (aligned : beforeLabels.length = before.blocks.length)
    (root : RootId) :
    lineageElements after afterLabels root =
      lineageElements before beforeLabels root := by
  rcases historyStep with ⟨step, labels_eq⟩
  rw [labels_eq]
  rw [RootLabels.after_split]
  rcases step with ⟨before_valid, effect, _after_valid⟩
  cases effect with
  | split found shrinking prefix_le blocks_eq values_eq =>
      rename_i source
      have global_nodup :
          (before.blocks.flatMap Block.elements).Nodup := by
        simpa [State.allElements] using before_valid.1
      obtain ⟨source_lt, _source_eq⟩ :=
        List.getElem?_eq_some_iff.mp found
      have source_label_lt : blockId < beforeLabels.length := by
        simpa [aligned] using source_lt
      let sourceRoot : RootId := beforeLabels[blockId]
      have source_root_found :
          beforeLabels[blockId]? = some sourceRoot :=
        List.getElem?_eq_getElem source_label_lt
      have emptied_eq :
          lineageElementsOf
              (before.blocks.modify blockId fun current =>
                { current with elements := [] })
              beforeLabels root =
            lineageElementsOf before.blocks beforeLabels root \
              if beforeLabels[blockId]? = some root then
                source.elements.toFinset
              else ∅ := by
        apply lineageElementsOf_modify_sdiff aligned global_nodup blockId
          found source.elements.toFinset
        · exact Finset.Subset.rfl
        · simp
      have children_eq :
          lineageElementsOf
              [{ source with
                  elements := source.elements.take prefixLength },
                { source with
                  elements := source.elements.drop prefixLength }]
              [sourceRoot, sourceRoot] root =
            if beforeLabels[blockId]? = some root then
              source.elements.toFinset
            else ∅ := by
        rw [source_root_found]
        by_cases same_root : sourceRoot = root
        · subst root
          simp only [if_pos, lineageElementsOf_cons,
            lineageElementsOf_nil_left, Finset.union_empty]
          exact toFinset_take_union_drop source.elements prefixLength
        · simp [lineageElementsOf, same_root]
      have removed_subset_payload :
          (if beforeLabels[blockId]? = some root then
              source.elements.toFinset
            else ∅) ⊆
            lineageElementsOf before.blocks beforeLabels root := by
        by_cases same_root : sourceRoot = root
        · subst root
          simpa [source_root_found] using
            (block_elements_subset_lineageElementsOf aligned found
              source_root_found)
        · simp [source_root_found, same_root]
      unfold lineageElements
      rw [blocks_eq]
      dsimp only [splitBlocks]
      rw [lineageElementsOf_append (by simpa using aligned)]
      rw [emptied_eq]
      have fallback_eq :
          (RootLabels.root? beforeLabels blockId).getD blockId =
            sourceRoot := by
        simp [RootLabels.root?, source_root_found]
      rw [fallback_eq]
      rw [children_eq]
      exact Finset.sdiff_union_of_subset removed_subset_payload

/-- Unit value changes do not alter any block or lineage payload. -/
theorem lineageElements_valueChange
    {n : ℕ} {params : Parameters}
    {before after : State n} {beforeLabels afterLabels : RootLabels}
    {element : Element n} {delta : ValueDelta}
    (historyStep :
      HistoryStep params before beforeLabels (.valueChange element delta)
        after afterLabels)
    (root : RootId) :
    lineageElements after afterLabels root =
      lineageElements before beforeLabels root := by
  rcases historyStep with ⟨step, labels_eq⟩
  rw [labels_eq]
  rcases step with ⟨_before_valid, effect, _after_valid⟩
  cases effect with
  | decrease can_decrease blocks_eq values_eq =>
      simp [lineageElements, blocks_eq, RootLabels.after]
  | increase can_increase blocks_eq values_eq =>
      simp [lineageElements, blocks_eq, RootLabels.after]

/-- Pointwise membership form of the exact insert update. -/
theorem mem_lineageElements_insert_iff
    {n : ℕ} {params : Parameters}
    {before after : State n} {beforeLabels afterLabels : RootLabels}
    {blockId : BlockId} {element queried : Element n}
    (historyStep :
      HistoryStep params before beforeLabels (.insert blockId element)
        after afterLabels)
    (aligned : beforeLabels.length = before.blocks.length)
    (root : RootId) :
    queried ∈ lineageElements after afterLabels root ↔
      queried ∈ lineageElements before beforeLabels root ∨
        (RootLabels.root? beforeLabels blockId = some root ∧
          queried = element) := by
  rw [historyStep.lineageElements_insert aligned root]
  by_cases root_eq :
      RootLabels.root? beforeLabels blockId = some root
  · simp [root_eq, eq_comm]
    exact or_comm
  · simp [root_eq]

/-- Pointwise membership form of the exact delete update. -/
theorem mem_lineageElements_delete_iff
    {n : ℕ} {params : Parameters}
    {before after : State n} {beforeLabels afterLabels : RootLabels}
    {blockId : BlockId} {element queried : Element n}
    (historyStep :
      HistoryStep params before beforeLabels (.delete blockId element)
        after afterLabels)
    (aligned : beforeLabels.length = before.blocks.length)
    (root : RootId) :
    queried ∈ lineageElements after afterLabels root ↔
      queried ∈ lineageElements before beforeLabels root ∧
        queried ∉
          (if RootLabels.root? beforeLabels blockId = some root then
            ({element} : Finset (Element n))
          else (∅ : Finset (Element n))) := by
  rw [historyStep.lineageElements_delete aligned root]
  simp only [Finset.mem_sdiff]

/-- Pointwise transfer law for a pass, suitable for trace induction. -/
theorem mem_lineageElements_pass_iff
    {n : ℕ} {params : Parameters}
    {before after : State n} {beforeLabels afterLabels : RootLabels}
    {blockId : BlockId} {matching : List (Pairing n)}
    {queried : Element n}
    (historyStep :
      HistoryStep params before beforeLabels (.pass blockId matching)
        after afterLabels)
    (aligned : beforeLabels.length = before.blocks.length)
    (root : RootId) :
    queried ∈ lineageElements after afterLabels root ↔
      (queried ∈ lineageElements before beforeLabels root ∧
          queried ∉
            sourceLineageLosers beforeLabels blockId matching root) ∨
        queried ∈
          destinationLineageLosers beforeLabels matching root := by
  rw [historyStep.lineageElements_pass aligned root]
  simp only [Finset.mem_union, Finset.mem_sdiff]

/-- An insertion grows its actual target lineage by exactly one element. -/
theorem lineageSize_insert_at_root
    {n : ℕ} {params : Parameters}
    {before after : State n} {beforeLabels afterLabels : RootLabels}
    {blockId : BlockId} {element : Element n}
    (historyStep :
      HistoryStep params before beforeLabels (.insert blockId element)
        after afterLabels)
    (aligned : beforeLabels.length = before.blocks.length)
    {targetRoot : RootId}
    (root_found :
      RootLabels.root? beforeLabels blockId = some targetRoot) :
    lineageSize after afterLabels targetRoot =
      lineageSize before beforeLabels targetRoot + 1 := by
  have update :=
    historyStep.lineageElements_insert aligned targetRoot
  have element_unassigned : element ∉ before.allElements := by
    cases historyStep.step.2.1 with
    | insert found growing unassigned value_order blocks_eq values_eq =>
        exact unassigned
  have element_absent :
      element ∉ lineageElements before beforeLabels targetRoot := by
    intro member
    apply element_unassigned
    change element ∈ before.blocks.flatMap Block.elements
    exact mem_flatMap_elements_of_mem_lineageElementsOf member
  unfold lineageSize
  rw [update, root_found]
  simp only [if_pos, Finset.union_singleton]
  exact Finset.card_insert_of_notMem element_absent

/-- A deletion shrinks its actual source lineage by exactly one element. -/
theorem lineageSize_delete_at_root
    {n : ℕ} {params : Parameters}
    {before after : State n} {beforeLabels afterLabels : RootLabels}
    {blockId : BlockId} {element : Element n}
    (historyStep :
      HistoryStep params before beforeLabels (.delete blockId element)
        after afterLabels)
    (aligned : beforeLabels.length = before.blocks.length)
    {sourceRoot : RootId}
    (root_found :
      RootLabels.root? beforeLabels blockId = some sourceRoot) :
    lineageSize after afterLabels sourceRoot + 1 =
      lineageSize before beforeLabels sourceRoot := by
  have update :=
    historyStep.lineageElements_delete aligned sourceRoot
  rcases historyStep.step with ⟨_before_valid, effect, _after_valid⟩
  cases effect with
  | delete found shrinking present blocks_eq values_eq =>
      rename_i block
      have element_present :
          element ∈ lineageElements before beforeLabels sourceRoot :=
        (mem_lineageElements_iff aligned).mpr
          ⟨blockId, block, found, root_found, present⟩
      unfold lineageSize
      rw [update, root_found]
      simp only [if_pos, Finset.sdiff_singleton_eq_erase]
      exact Finset.card_erase_add_one element_present

/-- A pass can grow a lineage only by losers delivered to that lineage. -/
theorem lineageSize_pass_le
    {n : ℕ} {params : Parameters}
    {before after : State n} {beforeLabels afterLabels : RootLabels}
    {blockId : BlockId} {matching : List (Pairing n)}
    (historyStep :
      HistoryStep params before beforeLabels (.pass blockId matching)
        after afterLabels)
    (aligned : beforeLabels.length = before.blocks.length)
    (root : RootId) :
    lineageSize after afterLabels root ≤
      lineageSize before beforeLabels root +
        (destinationLineageLosers beforeLabels matching root).card := by
  have update := historyStep.lineageElements_pass aligned root
  unfold lineageSize
  rw [update]
  calc
    ((lineageElements before beforeLabels root \
          sourceLineageLosers beforeLabels blockId matching root) ∪
        destinationLineageLosers beforeLabels matching root).card ≤
        (lineageElements before beforeLabels root \
            sourceLineageLosers beforeLabels blockId matching root).card +
          (destinationLineageLosers beforeLabels matching root).card :=
      Finset.card_union_le _ _
    _ ≤ (lineageElements before beforeLabels root).card +
          (destinationLineageLosers beforeLabels matching root).card :=
      Nat.add_le_add_right
        (Finset.card_le_card Finset.sdiff_subset) _

/-- Split preserves lineage cardinality, not merely total block cardinality. -/
theorem lineageSize_split
    {n : ℕ} {params : Parameters}
    {before after : State n} {beforeLabels afterLabels : RootLabels}
    {blockId prefixLength : BlockId}
    (historyStep :
      HistoryStep params before beforeLabels
        (.split blockId prefixLength) after afterLabels)
    (aligned : beforeLabels.length = before.blocks.length)
    (root : RootId) :
    lineageSize after afterLabels root =
      lineageSize before beforeLabels root := by
  unfold lineageSize
  rw [historyStep.lineageElements_split aligned root]

end HistoryStep

end Splay.Interface

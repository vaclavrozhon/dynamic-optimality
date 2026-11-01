import Greedy.GrowthPersistence
import FrozenFamilyHistory

/-!
# Stored frozen fragments are covered by historical growth batches

A frozen block is covered when all of its immutable join times occur in
one creator-slot batch with the same family name. A constant join time is
also allowed: such a family has identically zero signed creator coefficient,
and includes freshly paid singleton families.
-/

namespace Greedy.GrowthJournal

open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Lazy.Canonical
open GreedyMerge.OrderedBlocks GreedyMerge.Primitives GreedyMerge.HeapAllocation
open GreedyMerge.GrowthBook GreedyMerge.GrowthWindows

def InBatch {n : ℕ} (books : HeapBooks n) (block : Frozen) : Prop :=
  ∃ creator side, creator.val = block.creator ∧
    ∀ entry ∈ block.members, entry.joined ∈ collect block.family (journal (books creator side))

def OneTime (block : Frozen) : Prop :=
  ∀ first ∈ block.members, ∀ second ∈ block.members, first.joined = second.joined

def Covered {n : ℕ} (books : HeapBooks n) (block : Frozen) : Prop := InBatch books block ∨ OneTime block

def HeapCovered {n : ℕ} (books : HeapBooks n) (states : HeapSides n) : Prop :=
  ∀ owner side block, block ∈ (states owner side).shrinking → Covered books block

theorem Covered.mono {n : ℕ} {first last : HeapBooks n} {block : Frozen}
    (covered : Covered first block) (extension : HeapExtends first last) : Covered last block := by
  rcases covered with ⟨creator, side, correct, times⟩ | constant
  · exact Or.inl ⟨creator, side, correct, fun entry member => extension creator side _ _ (times entry member)⟩
  · exact Or.inr constant

theorem Covered.descends {n : ℕ} {books : HeapBooks n} {before after : Frozen}
    (covered : Covered books before) (descends : Descends after before) : Covered books after := by
  rcases covered with ⟨creator, side, correct, times⟩ | constant
  · refine Or.inl ⟨creator, side, correct.trans descends.2.1.symm, ?_⟩
    intro entry member
    rw [descends.1]
    exact times entry (descends.2.2.subset member)
  · exact Or.inr (fun first firstMem second secondMem =>
      constant first (descends.2.2.subset firstMem) second (descends.2.2.subset secondMem))

theorem singleton_covered {n : ℕ} (books : HeapBooks n) (id family owner base : ℕ) (entry : Entry) :
    Covered books (singleton id family owner base entry) := by
  right
  intro first firstMem second secondMem
  have firstEq : first = entry := List.mem_singleton.mp firstMem
  have secondEq : second = entry := List.mem_singleton.mp secondMem
  simp [firstEq, secondEq]

theorem freeze_covered {n : ℕ} (books : HeapBooks n) (owner : External n) (side : Bool)
    (state : SideState) (grower : Grower) (present : state.grower = some grower)
    (matched : Matches state (books owner side)) (creator : grower.creator = owner.val) (id base : ℕ) :
    Covered books (freeze id base grower) := by
  obtain ⟨actual, actualPresent, current⟩ := matched
  have equal := Option.some.inj (actualPresent.symm.trans present)
  subst actual
  refine Or.inl ⟨owner, side, creator.symm, ?_⟩
  intro entry member
  apply (collect_member grower.family entry.joined (journal (books owner side))).mpr
  refine ⟨(books owner side).current, by simp [journal], ?_, ?_⟩
  · rw [current]; rfl
  · rw [current]
    exact List.mem_map.mpr ⟨entry, member, rfl⟩

theorem convert_covered {n : ℕ} (books finalBooks : HeapBooks n) (owner : External n) (side : Bool)
    (state : SideState) (family id base : ℕ)
    (covered : ∀ block ∈ state.shrinking, Covered books block)
    (matched : Matches state (books owner side))
    (creator : ∀ grower, state.grower = some grower → grower.creator = owner.val)
    (extension : HeapExtends books finalBooks) :
    ∀ block ∈ (convert owner.val family id base state).shrinking, Covered finalBooks block := by
  intro block member
  cases present : state.grower with
  | none => exact (covered block (by simpa [convert, present] using member)).mono extension
  | some grower =>
      by_cases empty : grower.members = []
      · exact (covered block (by simpa [convert, present, empty] using member)).mono extension
      · simp only [convert, present, empty, ↓reduceIte, List.mem_append, List.mem_singleton] at member
        rcases member with old | same
        · exact (covered block old).mono extension
        · subst block
          exact (freeze_covered books owner side state grower present matched (creator grower present) grower.id base).mono extension

theorem installPaid_covered {n : ℕ} (books : HeapBooks n) (owner : ℕ) (side : Bool)
    (splitStart id family base : ℕ) (entry : Entry) (state : SideState)
    (covered : ∀ block ∈ state.shrinking, Covered books block) :
    ∀ block ∈ (installPaid owner side splitStart id family base entry state).shrinking, Covered books block := by
  intro block member
  change block ∈ (separateOuter side entry.key splitStart state).1 ++
    [singleton id family owner base entry] ++ (separateOuter side entry.key splitStart state).2 at member
  rcases List.mem_append.mp member with first | last
  · rcases List.mem_append.mp first with old | new
    · obtain ⟨original, originalMem, descendant⟩ := separateOuter_descends side entry.key splitStart state block
        (List.mem_append_left _ old)
      exact (covered original originalMem).descends descendant
    · have equal := List.mem_singleton.mp new
      subst block
      exact singleton_covered books id family owner base entry
  · obtain ⟨original, originalMem, descendant⟩ := separateOuter_descends side entry.key splitStart state block
      (List.mem_append_right _ last)
    exact (covered original originalMem).descends descendant

theorem initial_covered {n : ℕ} (snapshot : Snapshot n) (tree : BST 0 n) (K : ℤ) :
    HeapCovered (GreedyMerge.GrowthBook.initial snapshot tree K) (GreedyMerge.InitialBlocks.state snapshot tree K) := by
  intro owner side block member
  simp [GreedyMerge.InitialBlocks.state] at member

end Greedy.GrowthJournal

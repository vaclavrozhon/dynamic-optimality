import Mathlib

/-!
Numerical offset transport and the local ordered-singleton insertion
primitive. This file does not construct the geometric comparator update,
count its affected blocks, or formalize the full history-ledger theorem.
-/

namespace GreedyMerge.Primitives

def transportedOffset (delta change : ℝ) : ℝ := max 0 (delta + change)

/-- Uniform offset transport is valid and cannot increase point gaps.
The offset need not be an integer. -/
theorem offset_transport (gap delta change : ℝ)
    (_hdelta : 0 ≤ delta) (hvalid : delta ≤ gap)
    (hfinal : 0 ≤ gap + change) :
    0 ≤ transportedOffset delta change ∧
      transportedOffset delta change ≤ gap + change ∧
      0 ≤ gap + change - transportedOffset delta change ∧
      gap + change - transportedOffset delta change ≤ gap - delta := by
  rcases le_total 0 (delta + change) with h | h
  · rw [transportedOffset, max_eq_right h]
    constructor
    · exact h
    constructor
    · linarith
    constructor <;> linarith
  · rw [transportedOffset, max_eq_left h]
    constructor
    · exact le_refl 0
    constructor
    · exact hfinal
    constructor <;> linarith

/-- The two-stage old-rank owner move followed by rank update is also
valid and nonincreasing, whenever the intermediate true gaps are valid. -/
theorem offset_transport_twice (gap delta first second : ℝ)
    (hdelta : 0 ≤ delta) (hvalid : delta ≤ gap)
    (hmid : 0 ≤ gap + first) (hfinal : 0 ≤ gap + first + second) :
    let middle := transportedOffset delta first
    let final := transportedOffset middle second
    0 ≤ final ∧ final ≤ gap + first + second ∧
      gap + first + second - final ≤ gap - delta := by
  dsimp
  obtain ⟨h0, hv, _, hd⟩ := offset_transport gap delta first hdelta hvalid hmid
  obtain ⟨h0', hv', _, hd'⟩ :=
    offset_transport (gap + first) (transportedOffset delta first) second h0 hv hfinal
  exact ⟨h0', hv', le_trans hd' hd⟩

/-- Pointwise version for an arbitrary block, with one common shift. -/
theorem block_offset_transport {ι : Type*} (members : Set ι)
    (gap : ι → ℝ) (delta change : ℝ)
    (hdelta : 0 ≤ delta)
    (hvalid : ∀ v ∈ members, delta ≤ gap v)
    (hfinal : ∀ v ∈ members, 0 ≤ gap v + change) :
    ∀ v ∈ members,
      0 ≤ gap v + change - transportedOffset delta change ∧
      gap v + change - transportedOffset delta change ≤ gap v - delta := by
  intro v hv
  exact (offset_transport (gap v) delta change hdelta (hvalid v hv) (hfinal v hv)).2.2

theorem paid_label_increase (old new K : ℤ)
    (hold : 1 ≤ old) (hnew : new ≤ K) :
    max 0 (new-old) ≤ max 0 (K-1) := by
  exact max_le_max le_rfl (by omega)

/- A history record is immutable; split blocks carry these same records. -/
structure Entry where
  key : ℕ
  joined : ℕ
  entryLabel : ℤ
  creatorLabel : ℤ
  deriving DecidableEq

structure Block where
  creator : ℕ
  family : ℕ
  growing : Bool
  members : List Entry
  deriving DecidableEq

def splitLeft (b : Block) (k : ℕ) : Block :=
  { b with members := b.members.take k }

def splitRight (b : Block) (k : ℕ) : Block :=
  { b with members := b.members.drop k }

def singleton (creator family : ℕ) (entry : Entry) : Block :=
  ⟨creator, family, false, [entry]⟩

def allShrinking (bs : List Block) : Prop :=
  ∀ b ∈ bs, b.growing = false

def orderedRecords (es : List Entry) : Prop :=
  es.Pairwise (fun a b => a.key < b.key)

theorem split_preserves_creator_family (b : Block) (k : ℕ) :
    (splitLeft b k).creator = b.creator ∧
    (splitRight b k).creator = b.creator ∧
    (splitLeft b k).family = b.family ∧
    (splitRight b k).family = b.family := by
  simp [splitLeft, splitRight]

/-- Splitting retains the exact immutable entry records, including all
entry labels and times. There is no rewritten snapshot or merged family. -/
theorem split_preserves_exact_histories (b : Block) (k : ℕ) :
    (splitLeft b k).members ++ (splitRight b k).members = b.members := by
  simp [splitLeft, splitRight]

theorem allShrinking_append (a b : List Block) :
    allShrinking (a ++ b) ↔ allShrinking a ∧ allShrinking b := by
  simp only [allShrinking, List.mem_append]
  aesop

/-- Splitting a shrinking block and inserting a fresh shrinking singleton
leaves every preexisting grower farther outward untouched. -/
theorem singleton_preserves_shrinking_prefix
    (pre post : List Block) (focus : Block) (k creator family : ℕ) (entry : Entry)
    (hpre : allShrinking pre) (hpost : allShrinking post)
    (hfocus : focus.growing = false) :
    allShrinking
      (pre ++ [splitLeft focus k, singleton creator family entry,
                splitRight focus k] ++ post) := by
  simp only [allShrinking_append]
  refine ⟨⟨hpre, ?_⟩, hpost⟩
  simpa [allShrinking, splitLeft, splitRight, singleton] using hfocus

/-- The replacement creates exactly two additional blocks: one split
piece and one paid singleton. Empty pieces may simply be discarded. -/
theorem singleton_block_count (pre post : List Block) (focus : Block)
    (k creator family : ℕ) (entry : Entry) :
    (pre ++ [splitLeft focus k, singleton creator family entry,
              splitRight focus k] ++ post).length =
      (pre ++ [focus] ++ post).length + 2 := by
  simp
  omega

theorem ordered_insert (pre post : List Entry) (entry : Entry)
    (hpre : orderedRecords pre) (hpost : orderedRecords post)
    (hleft : ∀ x ∈ pre, x.key < entry.key)
    (hright : ∀ x ∈ post, entry.key < x.key) :
    orderedRecords (pre ++ entry :: post) := by
  apply List.pairwise_append.mpr
  refine ⟨hpre, ?_, ?_⟩
  · exact List.pairwise_cons.mpr ⟨hright, hpost⟩
  · intro x hx y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · exact hleft x hx
    · exact Nat.lt_trans (hleft x hx) (hright y hy)

/- The outermost-grower consequence is stated with a shrinking prefix:
the distinguished final grower is exactly the final list element. -/
theorem singleton_preserves_outer_grower
    (pre post : List Block) (focus grower : Block)
    (k creator family : ℕ) (entry : Entry)
    (hpre : allShrinking pre) (hpost : allShrinking post)
    (hfocus : focus.growing = false) (hgrow : grower.growing = true) :
    ∃ front, allShrinking front ∧
      pre ++ [splitLeft focus k, singleton creator family entry,
               splitRight focus k] ++ post ++ [grower] = front ++ [grower] ∧
      grower.growing = true := by
  refine ⟨_, singleton_preserves_shrinking_prefix pre post focus k creator family entry
    hpre hpost hfocus, rfl, hgrow⟩

end GreedyMerge.Primitives

#print axioms GreedyMerge.Primitives.offset_transport
#print axioms GreedyMerge.Primitives.offset_transport_twice
#print axioms GreedyMerge.Primitives.block_offset_transport
#print axioms GreedyMerge.Primitives.singleton_preserves_outer_grower
#print axioms GreedyMerge.Primitives.ordered_insert

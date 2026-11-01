import OrderedBlockCuts
import OrderedBlockNumerics

/-!
Concrete conversion of exactly the persistent growers whose member and
owner have different comparator-rank shifts. The number of newly created
replacement families is derived from the actual shallow cut census.
-/
namespace GreedyMerge.OrderedBlocks

open GreedyMerge.Primitives (Entry)
open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Lazy.Canonical
open GreedyMerge.AdminCuts

def rankShift {n : ℕ} (before after : BST 0 n) (key : ℕ) : ℤ :=
  (after.externalDepth key : ℤ) - before.externalDepth key

def GrowerMismatch {n : ℕ} (before after : BST 0 n)
    (owner : External n) (state : SideState) : Prop :=
  match state.grower with
  | none => False
  | some grower => ∃ entry ∈ grower.members,
      rankShift before after entry.key ≠ rankShift before after owner.val

instance growerMismatchDecidable {n : ℕ} (before after : BST 0 n)
    (owner : External n) (state : SideState) : Decidable (GrowerMismatch before after owner state) := by
  unfold GrowerMismatch
  cases state.grower <;> infer_instance

theorem grower_member_entries {state : SideState} {grower : Grower}
    (someGrower : state.grower = some grower) {entry : Entry}
    (member : entry ∈ grower.members) : entry ∈ entries state := by
  apply List.mem_append_right
  simpa only [someGrower, growerEntries] using member

theorem growerMismatch_nonempty {n : ℕ} {before after : BST 0 n}
    {owner : External n} {state : SideState}
    (mismatch : GrowerMismatch before after owner state) :
    ∃ grower, state.grower = some grower ∧ grower.members ≠ [] := by
  cases h : state.grower with
  | none => simp [GrowerMismatch, h] at mismatch
  | some grower =>
      simp only [GrowerMismatch, h] at mismatch
      obtain ⟨entry, member, _⟩ := mismatch
      exact ⟨grower, rfl, List.ne_nil_of_mem member⟩

theorem growerMismatch_supported {n depth : ℕ} {before after : BST 0 n}
    (profile : RotationCutProfile before after depth) (tree : BST 0 n)
    {owner : External n} {state : SideState}
    (sound : ParentSound (Snapshot.ofTree before) tree owner state)
    (mismatch : GrowerMismatch before after owner state) :
    ∃ entry, (entry, owner) ∈ cutOwnerIncidences profile tree := by
  cases h : state.grower with
  | none => simp [GrowerMismatch, h] at mismatch
  | some grower =>
      simp only [GrowerMismatch, h] at mismatch
      obtain ⟨entry, member, different⟩ := mismatch
      obtain ⟨record, keyEq, parent⟩ := sound entry (grower_member_entries h member)
      apply parent_shift_supported profile tree parent
      unfold rankShift at different
      rw [keyEq]
      exact different.symm

def prepareGrower {n : ℕ} (before after : BST 0 n) (owner : External n)
    (freshFamily freshId : ℕ) (state : SideState) : SideState :=
  if GrowerMismatch before after owner state then
    convert owner.val freshFamily freshId (before.externalDepth owner.val) state
  else state

def growerPreparationBirths {n : ℕ} (before after : BST 0 n)
    (owner : External n) (state : SideState) : ℕ :=
  if GrowerMismatch before after owner state then conversionBirths state else 0

theorem prepareGrower_entries {n : ℕ} (before after : BST 0 n) (owner : External n)
    (freshFamily freshId : ℕ) (state : SideState) :
    entries (prepareGrower before after owner freshFamily freshId state) = entries state := by
  unfold prepareGrower
  split_ifs <;> simp

theorem prepareGrower_valid {n : ℕ} (before after : BST 0 n) (owner : External n)
    (freshFamily freshId : ℕ) (side : Bool) (state : SideState)
    (valid : Valid owner.val side state) :
    Valid owner.val side (prepareGrower before after owner freshFamily freshId state) := by
  unfold prepareGrower
  split_ifs
  · exact conversion_valid owner.val freshFamily freshId _ side state valid
  · exact valid

theorem prepareGrower_resolves {n : ℕ} (before after : BST 0 n) (owner : External n)
    (freshFamily freshId : ℕ) (state : SideState) :
    ¬ GrowerMismatch before after owner (prepareGrower before after owner freshFamily freshId state) := by
  unfold prepareGrower
  split_ifs with mismatch
  · obtain ⟨grower, same, nonempty⟩ := growerMismatch_nonempty mismatch
    simp [convert, same, nonempty, GrowerMismatch, emptyGrower]
  · exact mismatch

theorem prepareGrower_births_exact {n : ℕ} (before after : BST 0 n) (owner : External n)
    (freshFamily freshId : ℕ) (state : SideState) :
    (prepareGrower before after owner freshFamily freshId state).shrinking.length =
      state.shrinking.length + growerPreparationBirths before after owner state := by
  unfold prepareGrower growerPreparationBirths
  split_ifs
  · exact conversion_births_exact ..
  · simp

theorem growerPreparationBirths_eq {n : ℕ} (before after : BST 0 n)
    (owner : External n) (state : SideState) :
    growerPreparationBirths before after owner state =
      if GrowerMismatch before after owner state then 1 else 0 := by
  unfold growerPreparationBirths
  split_ifs with mismatch
  · obtain ⟨grower, same, nonempty⟩ := growerMismatch_nonempty mismatch
    simp [conversionBirths, same, nonempty]
  · rfl

noncomputable def supportedOwners {n depth : ℕ} {before after : BST 0 n}
    (profile : RotationCutProfile before after depth) (tree : BST 0 n) : Finset (External n) :=
  (cutOwnerIncidences profile tree).image Prod.snd

noncomputable def allGrowerPreparationBirths {n : ℕ} (before after : BST 0 n)
    (states : External n → Bool → SideState) : ℕ :=
  ∑ owner, (growerPreparationBirths before after owner (states owner false) +
    growerPreparationBirths before after owner (states owner true))

/-- Exactly selected conversions cost at most two replacements for each
owner occurring in the concrete shallow cut/owner support. -/
theorem allGrowerPreparationBirths_le {n depth : ℕ} {before after : BST 0 n}
    (profile : RotationCutProfile before after depth) (tree : BST 0 n)
    (states : External n → Bool → SideState)
    (sound : ∀ owner side, ParentSound (Snapshot.ofTree before) tree owner (states owner side)) :
    allGrowerPreparationBirths before after states ≤ 2 * (depth+2)^2 := by
  classical
  have supported {owner : External n} {side : Bool}
      (mismatch : GrowerMismatch before after owner (states owner side)) :
      owner ∈ supportedOwners profile tree := by
    obtain ⟨entry, member⟩ := growerMismatch_supported profile tree (sound owner side) mismatch
    exact Finset.mem_image.mpr ⟨(entry, owner), member, rfl⟩
  have pointwise : ∀ owner,
      growerPreparationBirths before after owner (states owner false) +
        growerPreparationBirths before after owner (states owner true) ≤
      if owner ∈ supportedOwners profile tree then 2 else 0 := by
    intro owner
    rw [growerPreparationBirths_eq, growerPreparationBirths_eq]
    by_cases member : owner ∈ supportedOwners profile tree
    · rw [if_pos member]
      split_ifs <;> omega
    · have left : ¬ GrowerMismatch before after owner (states owner false) := fun h => member (supported h)
      have right : ¬ GrowerMismatch before after owner (states owner true) := fun h => member (supported h)
      simp [member, left, right]
  calc
    allGrowerPreparationBirths before after states ≤
        ∑ owner : External n, if owner ∈ supportedOwners profile tree then 2 else 0 :=
      Finset.sum_le_sum fun owner _ => pointwise owner
    _ = 2 * (supportedOwners profile tree).card := by simp [Finset.sum_ite_mem, Nat.mul_comm]
    _ ≤ 2 * (depth+2)^2 := by
      apply Nat.mul_le_mul_left
      exact Finset.card_image_le.trans (cut_owner_incidence_card profile tree)

#print axioms prepareGrower_resolves
#print axioms allGrowerPreparationBirths_le

end GreedyMerge.OrderedBlocks

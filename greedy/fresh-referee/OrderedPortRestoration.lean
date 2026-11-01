import OrderedJunctionTransfer
import HeapBlockCoverage

/-!
Restore paid ports under their actual final canonical parents. The side and
insertion position are computed; a global root is skipped. The spatial
constructor consumes supplied immutable entry snapshots, whose chronological
realization is the separate journal interface.
-/
namespace GreedyMerge.OrderedBlocks

open GreedyMerge.Primitives (Entry)
open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Lazy.Canonical
open GreedyMerge.BlockCoverage (Represented Sound CompleteExcept Complete)

structure PaidNames where
  replacementFamily : ℕ
  replacementId : ℕ
  splitStart : ℕ
  paidId : ℕ
  paidFamily : ℕ

def replaceSide {n : ℕ} (states : HeapSides n) (owner : External n) (side : Bool)
    (replacement : SideState) : HeapSides n :=
  fun current currentSide => if current = owner ∧ currentSide = side then replacement else states current currentSide

noncomputable def restorePort {n : ℕ} (snapshot : Snapshot n) (tree : BST 0 n)
    (names : PaidNames) (makeEntry : External n → Entry) (record : External n)
    (states : HeapSides n) : HeapSides n × ℕ :=
  match canonicalParent snapshot tree record with
  | none => (states, 0)
  | some owner =>
      let side := decide (record.val < owner.val)
      let entry := makeEntry owner
      let replacement := paidInsertion owner.val side names.replacementFamily names.replacementId
        names.splitStart names.paidId names.paidFamily (snapshot.rank owner) entry (states owner side)
      (replaceSide states owner side replacement,
       paidInsertionBirths owner.val names.replacementFamily names.replacementId
         (snapshot.rank owner) entry (states owner side))

theorem parent_key_different {n : ℕ} (snapshot : Snapshot n) (tree : BST 0 n)
    (record owner : External n) (parent : canonicalParent snapshot tree record = some owner) :
    record.val ≠ owner.val := by
  intro same
  have records : record = owner := Fin.ext same
  have lower := rank_canonicalParent_lt snapshot tree parent
  rw [records] at lower
  omega

theorem actual_parent_side {n : ℕ} (snapshot : Snapshot n) (tree : BST 0 n)
    (record owner : External n) (parent : canonicalParent snapshot tree record = some owner)
    (entry : Entry) (key : entry.key = record.val) :
    onSide owner.val (decide (record.val < owner.val)) entry := by
  have different := parent_key_different snapshot tree record owner parent
  by_cases before : record.val < owner.val
  · simp [onSide, before, key]
  · simp [onSide, before, key]
    omega

theorem restorePort_valid {n : ℕ} (snapshot : Snapshot n) (tree : BST 0 n)
    (names : PaidNames) (makeEntry : External n → Entry) (record : External n)
    (states : HeapSides n)
    (valid : ∀ owner side, Valid owner.val side (states owner side))
    (key : ∀ owner, (makeEntry owner).key = record.val)
    (absent : ¬ Represented states record.val) :
    ∀ owner side, Valid owner.val side ((restorePort snapshot tree names makeEntry record states).1 owner side) := by
  cases parent : canonicalParent snapshot tree record with
  | none => simpa [restorePort, parent] using valid
  | some actualOwner =>
      have localValid := paidInsertion_valid actualOwner.val (decide (record.val < actualOwner.val))
        names.replacementFamily names.replacementId names.splitStart names.paidId names.paidFamily
        (snapshot.rank actualOwner) (makeEntry actualOwner) (states actualOwner (decide (record.val < actualOwner.val)))
        (valid _ _) (actual_parent_side snapshot tree record actualOwner parent _ (key actualOwner))
        (by
          intro old member equal
          apply absent
          exact ⟨actualOwner, decide (record.val < actualOwner.val), old, member, equal.trans (key actualOwner)⟩)
      intro owner side
      simp only [restorePort, parent, replaceSide]
      split_ifs with location
      · obtain ⟨ownerEq, sideEq⟩ := location
        subst owner
        subst side
        exact localValid
      · exact valid owner side

theorem restorePort_sound {n : ℕ} (snapshot : Snapshot n) (tree : BST 0 n)
    (names : PaidNames) (makeEntry : External n → Entry) (record : External n)
    (states : HeapSides n)
    (valid : ∀ owner side, Valid owner.val side (states owner side))
    (sound : Sound snapshot tree states)
    (key : ∀ owner, (makeEntry owner).key = record.val) :
    Sound snapshot tree (restorePort snapshot tree names makeEntry record states).1 := by
  cases parent : canonicalParent snapshot tree record with
  | none => simpa [restorePort, parent] using sound
  | some actualOwner =>
      intro owner side entry member
      simp only [restorePort, parent, replaceSide] at member
      split_ifs at member with location
      · obtain ⟨ownerEq, sideEq⟩ := location
        subst owner
        subst side
        have permutation := paidInsertion_history_perm actualOwner.val (decide (record.val < actualOwner.val))
          names.replacementFamily names.replacementId names.splitStart names.paidId names.paidFamily
          (snapshot.rank actualOwner) (makeEntry actualOwner) _ (valid _ _)
        have choice := List.mem_cons.mp (permutation.mem_iff.mp member)
        rcases choice with rfl | oldMember
        · exact ⟨record, (key actualOwner).symm, parent⟩
        · exact sound actualOwner (decide (record.val < actualOwner.val)) entry oldMember
      · exact sound owner side entry member

theorem restorePort_births_le_four {n : ℕ} (snapshot : Snapshot n) (tree : BST 0 n)
    (names : PaidNames) (makeEntry : External n → Entry) (record : External n)
    (states : HeapSides n)
    (valid : ∀ owner side, Valid owner.val side (states owner side)) :
    (restorePort snapshot tree names makeEntry record states).2 ≤ 4 := by
  cases parent : canonicalParent snapshot tree record with
  | none => simp [restorePort, parent]
  | some owner =>
      simpa only [restorePort, parent] using paidInsertion_births_le_four owner.val
        (decide (record.val < owner.val)) names.replacementFamily names.replacementId
        (snapshot.rank owner) (makeEntry owner) _ (valid _ _)

/-- Restoration preserves every previous key and adds exactly the selected
nonroot port. This is enough to derive the complete final heap coverage. -/
theorem restorePort_represented {n : ℕ} (snapshot : Snapshot n) (tree : BST 0 n)
    (names : PaidNames) (makeEntry : External n → Entry) (record : External n)
    (states : HeapSides n)
    (valid : ∀ owner side, Valid owner.val side (states owner side))
    (key : ∀ owner, (makeEntry owner).key = record.val) (query : ℕ) :
    Represented (restorePort snapshot tree names makeEntry record states).1 query ↔
      Represented states query ∨
        (query = record.val ∧ canonicalParent snapshot tree record ≠ none) := by
  cases parent : canonicalParent snapshot tree record with
  | none => simp [restorePort, parent]
  | some actualOwner =>
      let selectedSide := decide (record.val < actualOwner.val)
      let newSide := paidInsertion actualOwner.val selectedSide names.replacementFamily names.replacementId
        names.splitStart names.paidId names.paidFamily (snapshot.rank actualOwner)
        (makeEntry actualOwner) (states actualOwner selectedSide)
      have permutation := paidInsertion_history_perm actualOwner.val selectedSide
        names.replacementFamily names.replacementId names.splitStart names.paidId names.paidFamily
        (snapshot.rank actualOwner) (makeEntry actualOwner) _ (valid _ _)
      have membership : ∀ entry, entry ∈ entries newSide ↔
          entry = makeEntry actualOwner ∨ entry ∈ entries (states actualOwner selectedSide) := by
        intro entry
        exact permutation.mem_iff.trans List.mem_cons
      simp only [restorePort, parent]
      change Represented (replaceSide states actualOwner selectedSide newSide) query ↔ _
      constructor
      · rintro ⟨owner, side, entry, member, equal⟩
        simp only [replaceSide] at member
        split_ifs at member with location
        · obtain ⟨ownerEq, sideEq⟩ := location
          subst owner
          subst side
          rcases (membership entry).mp member with rfl | oldMember
          · exact Or.inr ⟨equal.symm.trans (key actualOwner), by simp⟩
          · exact Or.inl ⟨actualOwner, selectedSide, entry, oldMember, equal⟩
        · exact Or.inl ⟨owner, side, entry, member, equal⟩
      · rintro (present | ⟨equal, _⟩)
        · obtain ⟨owner, side, entry, member, sameKey⟩ := present
          refine ⟨owner, side, entry, ?_, sameKey⟩
          simp only [replaceSide]
          split_ifs with location
          · obtain ⟨ownerEq, sideEq⟩ := location
            subst owner
            subst side
            exact (membership entry).mpr (Or.inr member)
          · exact member
        · refine ⟨actualOwner, selectedSide, makeEntry actualOwner, ?_, (key actualOwner).trans equal.symm⟩
          simp only [replaceSide, and_self, if_true]
          exact (membership _).mpr (Or.inl rfl)

noncomputable def restorePorts {n : ℕ} (snapshot : Snapshot n) (tree : BST 0 n)
    (names : ℕ → PaidNames) (makeEntry : ℕ → External n → External n → Entry) :
    List (External n) → ℕ → HeapSides n → HeapSides n × ℕ
  | [], _, states => (states, 0)
  | record :: rest, stage, states =>
      let head := restorePort snapshot tree (names stage) (makeEntry stage record) record states
      let tail := restorePorts snapshot tree names makeEntry rest (stage+1) head.1
      (tail.1, head.2 + tail.2)

/-- All list hypotheses are local data properties: distinct port keys and
initial absence. The cost is derived from actual singleton operations. -/
theorem restorePorts_valid_sound_births {n : ℕ} (snapshot : Snapshot n) (tree : BST 0 n)
    (names : ℕ → PaidNames) (makeEntry : ℕ → External n → External n → Entry)
    (key : ∀ stage record owner, (makeEntry stage record owner).key = record.val)
    (ports : List (External n)) (distinct : ports.Nodup) (stage : ℕ) (states : HeapSides n)
    (valid : ∀ owner side, Valid owner.val side (states owner side))
    (sound : Sound snapshot tree states)
    (absent : ∀ record ∈ ports, ¬ Represented states record.val) :
    (∀ owner side, Valid owner.val side ((restorePorts snapshot tree names makeEntry ports stage states).1 owner side)) ∧
    Sound snapshot tree (restorePorts snapshot tree names makeEntry ports stage states).1 ∧
    (restorePorts snapshot tree names makeEntry ports stage states).2 ≤ 4*ports.length := by
  induction ports generalizing stage states with
  | nil => exact ⟨valid, sound, by simp [restorePorts]⟩
  | cons record rest ih =>
      let head := restorePort snapshot tree (names stage) (makeEntry stage record) record states
      have headValid := restorePort_valid snapshot tree (names stage) (makeEntry stage record) record states
        valid (key stage record) (absent record (by simp))
      have headSound := restorePort_sound snapshot tree (names stage) (makeEntry stage record) record states
        valid sound (key stage record)
      have headBudget := restorePort_births_le_four snapshot tree (names stage) (makeEntry stage record) record states valid
      have tailAbsent : ∀ other ∈ rest, ¬ Represented head.1 other.val := by
        intro other member represented
        have choices := (restorePort_represented snapshot tree (names stage) (makeEntry stage record)
          record states valid (key stage record) other.val).mp represented
        rcases choices with old | ⟨sameKey, _⟩
        · exact absent other (by simp [member]) old
        · have same : other = record := Fin.ext sameKey
          have notMem := (List.nodup_cons.mp distinct).1
          exact notMem (by simpa only [same] using member)
      have tail := ih (List.nodup_cons.mp distinct).2 (stage+1) head.1 headValid headSound tailAbsent
      refine ⟨tail.1, tail.2.1, ?_⟩
      change head.2 + (restorePorts snapshot tree names makeEntry rest (stage+1) head.1).2 ≤ _
      change head.2 ≤ 4 at headBudget
      have tailBudget := tail.2.2
      simp only [List.length_cons]
      omega

theorem restorePorts_represented {n : ℕ} (snapshot : Snapshot n) (tree : BST 0 n)
    (names : ℕ → PaidNames) (makeEntry : ℕ → External n → External n → Entry)
    (key : ∀ stage record owner, (makeEntry stage record owner).key = record.val)
    (ports : List (External n)) (distinct : ports.Nodup) (stage : ℕ) (states : HeapSides n)
    (valid : ∀ owner side, Valid owner.val side (states owner side))
    (absent : ∀ record ∈ ports, ¬ Represented states record.val) (query : ℕ) :
    Represented (restorePorts snapshot tree names makeEntry ports stage states).1 query ↔
      Represented states query ∨ ∃ record ∈ ports,
        query = record.val ∧ canonicalParent snapshot tree record ≠ none := by
  induction ports generalizing stage states with
  | nil => simp [restorePorts]
  | cons record rest ih =>
      let head := restorePort snapshot tree (names stage) (makeEntry stage record) record states
      have headValid := restorePort_valid snapshot tree (names stage) (makeEntry stage record) record states
        valid (key stage record) (absent record (by simp))
      have tailAbsent : ∀ other ∈ rest, ¬ Represented head.1 other.val := by
        intro other member represented
        rcases (restorePort_represented snapshot tree (names stage) (makeEntry stage record)
          record states valid (key stage record) other.val).mp represented with old | ⟨sameKey, _⟩
        · exact absent other (by simp [member]) old
        · have same : other = record := Fin.ext sameKey
          exact (List.nodup_cons.mp distinct).1 (by simpa only [same] using member)
      change Represented (restorePorts snapshot tree names makeEntry rest (stage+1) head.1).1 query ↔ _
      rw [ih (List.nodup_cons.mp distinct).2 (stage+1) head.1 headValid tailAbsent]
      rw [restorePort_represented snapshot tree (names stage) (makeEntry stage record)
        record states valid (key stage record) query]
      simp only [List.mem_cons, exists_eq_or_imp]
      tauto

/-- Restoring all detached ports gives complete coverage of the actual
final canonical heap. Skipped ports are roots and need no membership. -/
theorem restorePorts_complete {n : ℕ} (snapshot : Snapshot n) (tree : BST 0 n)
    (names : ℕ → PaidNames) (makeEntry : ℕ → External n → External n → Entry)
    (key : ∀ stage record owner, (makeEntry stage record owner).key = record.val)
    (ports : List (External n)) (distinct : ports.Nodup) (stage : ℕ) (states : HeapSides n)
    (valid : ∀ owner side, Valid owner.val side (states owner side))
    (sound : Sound snapshot tree states)
    (absent : ∀ record ∈ ports, ¬ Represented states record.val)
    (complete : CompleteExcept snapshot tree states (ports.map Fin.val).toFinset) :
    Complete snapshot tree (restorePorts snapshot tree names makeEntry ports stage states).1 := by
  classical
  have finalSound := (restorePorts_valid_sound_births snapshot tree names makeEntry key ports distinct
    stage states valid sound absent).2.1
  intro record owner parent _
  apply BlockCoverage.represented_has_owner snapshot tree _ finalSound record owner parent
  apply (restorePorts_represented snapshot tree names makeEntry key ports distinct stage states valid
    absent record.val).mpr
  by_cases detached : record.val ∈ (ports.map Fin.val).toFinset
  · right
    obtain ⟨port, portMem, sameKey⟩ := List.mem_map.mp (List.mem_toFinset.mp detached)
    have equal : port = record := Fin.ext sameKey
    subst port
    exact ⟨record, portMem, rfl, by simp [parent]⟩
  · left
    obtain ⟨side, entry, member, equal⟩ := complete record owner parent detached
    exact ⟨owner, side, entry, member, equal⟩

#print axioms restorePort_valid
#print axioms restorePort_sound
#print axioms restorePort_represented
#print axioms restorePorts_valid_sound_births
#print axioms restorePorts_complete

end GreedyMerge.OrderedBlocks

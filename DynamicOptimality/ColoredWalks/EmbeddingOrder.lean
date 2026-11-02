import DynamicOptimality.ColoredWalks.EmbeddingMetric
import Mathlib.Data.List.Pairwise

/-! # Ordered color classes and their exposed endpoints

`Neighbors` refers to a fixed ordered set: no key of the same color lies
strictly between the two endpoints. `Extreme` means a first or last key
of a color in the current recursive interval.
-/

namespace DynamicOptimality.ColoredWalks

open ChaCha.MTR

variable {α β : Type*} [LinearOrder α]

def Extreme (color : α → β) (keys : List α) (key : α) : Prop :=
  key ∈ keys ∧ ((∀ other ∈ keys, color other = color key → key ≤ other) ∨
    (∀ other ∈ keys, color other = color key → other ≤ key))

structure Neighbors (color : α → β) (keys : List α) (first last : α) : Prop where
  first_mem : first ∈ keys
  last_mem : last ∈ keys
  increasing : first < last
  same : color first = color last
  consecutive : ∀ key ∈ keys, color key = color first → key ≤ first ∨ last ≤ key

theorem Extreme.restrict {color : α → β} {keys part : List α} {key : α}
    (extreme : Extreme color keys key) (subset : part ⊆ keys) (member : key ∈ part) :
    Extreme color part key := by
  refine ⟨member,?_⟩
  rcases extreme.2 with first | last
  · exact Or.inl (fun other present same => first other (subset present) same)
  · exact Or.inr (fun other present same => last other (subset present) same)

theorem Neighbors.restrict {color : α → β} {keys part : List α} {first last : α}
    (neighbors : Neighbors color keys first last) (subset : part ⊆ keys)
    (firstMember : first ∈ part) (lastMember : last ∈ part) :
    Neighbors color part first last :=
  ⟨firstMember,lastMember,neighbors.increasing,neighbors.same,
    fun key member same => neighbors.consecutive key (subset member) same⟩

theorem Neighbors.first_extreme {color : α → β} {keys part : List α} {first last : α}
    (neighbors : Neighbors color keys first last) (subset : part ⊆ keys)
    (member : first ∈ part) (below : ∀ key ∈ part, key < last) : Extreme color part first := by
  refine ⟨member,Or.inr ?_⟩
  intro key present same
  rcases neighbors.consecutive key (subset present) same with before | after
  · exact before
  · exact False.elim (not_lt_of_ge after (below key present))

theorem Neighbors.last_extreme {color : α → β} {keys part : List α} {first last : α}
    (neighbors : Neighbors color keys first last) (subset : part ⊆ keys)
    (member : last ∈ part) (above : ∀ key ∈ part, first < key) : Extreme color part last := by
  refine ⟨member,Or.inl ?_⟩
  intro key present same
  rcases neighbors.consecutive key (subset present) (same.trans neighbors.same.symm) with before | after
  · exact False.elim (not_lt_of_ge before (above key present))
  · exact after

def lowerKeys (keys : List α) (pivot : α) : List α := keys.filter (fun key => decide (key < pivot))
def upperKeys (keys : List α) (pivot : α) : List α := keys.filter (fun key => decide (pivot < key))

@[simp] theorem mem_lowerKeys {keys : List α} {pivot key : α} :
    key ∈ lowerKeys keys pivot ↔ key ∈ keys ∧ key < pivot := by simp [lowerKeys]

@[simp] theorem mem_upperKeys {keys : List α} {pivot key : α} :
    key ∈ upperKeys keys pivot ↔ key ∈ keys ∧ pivot < key := by simp [upperKeys]

theorem lowerKeys_subset (keys : List α) (pivot : α) : lowerKeys keys pivot ⊆ keys :=
  fun _ member => (mem_lowerKeys.mp member).1

theorem upperKeys_subset (keys : List α) (pivot : α) : upperKeys keys pivot ⊆ keys :=
  fun _ member => (mem_upperKeys.mp member).1

theorem lowerKeys_sublist (keys : List α) (pivot : α) : (lowerKeys keys pivot).Sublist keys :=
  List.filter_sublist

theorem upperKeys_sublist (keys : List α) (pivot : α) : (upperKeys keys pivot).Sublist keys :=
  List.filter_sublist

theorem lowerKeys_ordered {keys : List α} (ordered : keys.Pairwise (· < ·)) (pivot : α) :
    (lowerKeys keys pivot).Pairwise (· < ·) := ordered.sublist (lowerKeys_sublist keys pivot)

theorem upperKeys_ordered {keys : List α} (ordered : keys.Pairwise (· < ·)) (pivot : α) :
    (upperKeys keys pivot).Pairwise (· < ·) := ordered.sublist (upperKeys_sublist keys pivot)

theorem split_keys {keys : List α} (ordered : keys.Pairwise (· < ·)) {pivot : α}
    (member : pivot ∈ keys) : lowerKeys keys pivot ++ [pivot] ++ upperKeys keys pivot = keys := by
  obtain ⟨left,right,rfl⟩ := List.append_of_mem member
  have parts := List.pairwise_append.mp ordered
  have rightParts := List.pairwise_cons.mp parts.2.1
  have below : ∀ key ∈ left, key < pivot :=
    fun key present => parts.2.2 key present pivot List.mem_cons_self
  have above : ∀ key ∈ right, pivot < key := rightParts.1
  have lower : lowerKeys (left ++ pivot::right) pivot = left := by
    simp only [lowerKeys,List.filter_append,List.filter_cons,lt_self_iff_false,decide_false,Bool.false_eq_true,↓reduceIte]
    rw [List.filter_eq_self.mpr (fun key present => decide_eq_true (below key present))]
    have vanish : right.filter (fun key => decide (key < pivot)) = [] :=
      List.filter_eq_nil_iff.mpr (fun key present => by simp [not_lt_of_gt (above key present)])
    rw [vanish,List.append_nil]
  have upper : upperKeys (left ++ pivot::right) pivot = right := by
    simp only [upperKeys,List.filter_append,List.filter_cons,lt_self_iff_false,decide_false,Bool.false_eq_true,↓reduceIte]
    have vanish : left.filter (fun key => decide (pivot < key)) = [] :=
      List.filter_eq_nil_iff.mpr (fun key present => by simp [not_lt_of_gt (below key present)])
    rw [vanish,List.nil_append,List.filter_eq_self.mpr (fun key present => decide_eq_true (above key present))]
  rw [lower,upper]
  simp only [List.append_assoc,List.singleton_append]

theorem lowerKeys_shorter {keys : List α} (ordered : keys.Pairwise (· < ·)) {pivot : α}
    (member : pivot ∈ keys) : (lowerKeys keys pivot).length < keys.length := by
  have same := congrArg List.length (split_keys ordered member)
  simp only [List.length_append,List.length_singleton] at same
  omega

theorem upperKeys_shorter {keys : List α} (ordered : keys.Pairwise (· < ·)) {pivot : α}
    (member : pivot ∈ keys) : (upperKeys keys pivot).length < keys.length := by
  have same := congrArg List.length (split_keys ordered member)
  simp only [List.length_append,List.length_singleton] at same
  omega

theorem ordered_node {left right : RawTree α} {key : α} (ordered : Tree.Ordered (.node left key right)) :
    left.Ordered ∧ right.Ordered ∧ (∀ x ∈ left.inorder, x < key) ∧ (∀ x ∈ right.inorder, key < x) := by
  have outer := List.pairwise_append.mp ordered
  have inner := List.pairwise_append.mp outer.1
  exact ⟨inner.1,outer.2.1,fun x member => inner.2.2 x member key (by simp),
    fun x member => outer.2.2 key (by simp) x member⟩

/-- The root-depth guarantee for every color endpoint is the induction
invariant which prevents an extra logarithmic factor in the static metric. -/
structure Embedding (color : α → β) (keys : List α) (height : Nat) (tree : RawTree α) : Prop where
  word : tree.inorder = keys
  extreme : ∀ key, Extreme color keys key → ∃ depth, RootPath tree key depth ∧ depth < height
  neighbors : ∀ first last, Neighbors color keys first last → DistanceLE tree first last (4*height)

end DynamicOptimality.ColoredWalks

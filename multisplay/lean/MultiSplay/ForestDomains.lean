import MultiSplay.CommonForest

/-!
# Domain synchronization and component capacity

This layer forgets tree shapes, while retaining the complete ordered domains of
every split and join. The projection is proved from an actual forest execution.
It is the common interface for the splay execution and its offline comparator.
-/

namespace MultiSplay.CommonForest

open DynamicOptimality (RawTree)
open TangoSquared.MTR.Tree (inorder size length_inorder)

variable {α : Type*}

def domains (forest : List (RawTree α)) : List (List α) := forest.map inorder

def AccessPreserves (access : Access α) : Prop :=
  ∀ ⦃key a b work⦄, access key a b work → inorder a = inorder b

def PreparationPreserves (prepare : Preparation α) : Prop :=
  ∀ ⦃a b work⦄, prepare a b work → inorder a = inorder b

namespace Domains

inductive Step : List (List α) → List (Event α) → List (List α) → Prop
  | search (keys : List α) (key : α) : Step [keys] [.search keys key] [keys]
  | split (left : List α) (pivot : α) (right : List α) :
      Step [left ++ [pivot] ++ right] [.split left pivot right] [left, right]
  | join (left : List α) (pivot : α) (right : List α) :
      Step [left, right] [.join left pivot right] [left ++ [pivot] ++ right]
  | idle (keys : List α) : Step [keys] [] [keys]
  | context {a b : List (List α)} {word : List (Event α)}
      (step : Step a word b) (front back : List (List α)) :
      Step (front ++ a ++ back) word (front ++ b ++ back)
  | reorder {a b : List (List α)} (order : a.Perm b) : Step a [] b

inductive Trace : List (List α) → List (Event α) → List (List α) → Prop
  | nil (a : List (List α)) : Trace a [] a
  | cons {a b c : List (List α)} {first rest : List (Event α)}
      (step : Step a first b) (remaining : Trace b rest c) : Trace a (first ++ rest) c

def Capacity (bound : Nat) (forest : List (List α)) : Prop :=
  ∀ keys ∈ forest, keys.length ≤ bound

def JoinFits (bound : Nat) : Event α → Prop
  | .join left _ right => left.length + 1 + right.length ≤ bound
  | _ => True

theorem Step.capacity {a b : List (List α)} {word : List (Event α)}
    (step : Step a word b) {bound : Nat} (initial : Capacity bound a)
    (joins : ∀ event ∈ word, JoinFits bound event) : Capacity bound b := by
  induction step with
  | search => exact initial
  | split left pivot right =>
      have all := initial (left ++ [pivot] ++ right) (by simp)
      simp only [List.length_append, List.length_singleton] at all
      intro keys member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl <;> omega
  | join left pivot right =>
      have fits := joins (.join left pivot right) (by simp)
      intro keys member
      simp only [List.mem_singleton] at member
      subst keys
      simp only [List.length_append, List.length_singleton]
      change left.length + 1 + right.length ≤ bound at fits
      omega
  | idle => exact initial
  | @context a b word step front back ih =>
      have selected : Capacity bound a := by
        intro keys member
        exact initial keys (by simp [member])
      have result := ih selected joins
      intro keys member
      simp only [List.mem_append] at member
      rcases member with (inFront | inSelected) | inBack
      · exact initial keys (by simp [inFront])
      · exact result keys inSelected
      · exact initial keys (by simp [inBack])
  | reorder order =>
      intro keys member
      exact initial keys (order.mem_iff.mpr member)

theorem Trace.capacity {a b : List (List α)} {word : List (Event α)}
    (run : Trace a word b) {bound : Nat} (initial : Capacity bound a)
    (joins : ∀ event ∈ word, JoinFits bound event) : Capacity bound b := by
  induction run with
  | nil => exact initial
  | cons step remaining ih =>
      apply ih (step.capacity initial (fun event member => joins event (List.mem_append_left _ member)))
      intro event member
      exact joins event (List.mem_append_right _ member)

end Domains

theorem Step.toDomains {access : Access α} {prepare : Preparation α}
    (accessKeeps : AccessPreserves access) (prepareKeeps : PreparationPreserves prepare)
    {a b : List (RawTree α)} {word : List (Event α)} {work : Nat}
    (step : Step access prepare a word b work) : Domains.Step (domains a) word (domains b) := by
  induction step with
  | search execution =>
      simpa [domains, ← accessKeeps execution] using Domains.Step.search _ _
  | @split pivot a l r work execution =>
      have keys := accessKeeps execution
      simpa [domains, keys, inorder] using Domains.Step.split (inorder l) pivot (inorder r)
  | join l r pivot =>
      exact Domains.Step.join (inorder l) pivot (inorder r)
  | prepare execution =>
      simpa [domains, ← prepareKeeps execution] using Domains.Step.idle _
  | context step front back ih =>
      simpa [domains] using ih.context (domains front) (domains back)
  | reorder order => exact .reorder (order.map inorder)

theorem Trace.toDomains {access : Access α} {prepare : Preparation α}
    (accessKeeps : AccessPreserves access) (prepareKeeps : PreparationPreserves prepare)
    {a b : List (RawTree α)} {word : List (Event α)} {work : Nat}
    (run : Trace access prepare a word b work) : Domains.Trace (domains a) word (domains b) := by
  induction run with
  | nil => exact .nil _
  | cons step remaining ih => exact .cons (step.toDomains accessKeeps prepareKeeps) ih

theorem splay_preserves : AccessPreserves (Auxiliary.Splay : Access α) := by
  intro key a b work execution
  exact execution.inorder_eq

theorem idle_preserves : PreparationPreserves (idle : Preparation α) := by
  intro a b work h
  rw [h.1]

theorem SplayTrace.toDomains {a b : List (RawTree α)} {word : List (Event α)} {work : Nat}
    (run : SplayTrace a word b work) : Domains.Trace (domains a) word (domains b) :=
  Trace.toDomains splay_preserves idle_preserves run

def Capacity (bound : Nat) (forest : List (RawTree α)) : Prop :=
  ∀ tree ∈ forest, size tree ≤ bound

theorem capacity_iff_domains (bound : Nat) (forest : List (RawTree α)) :
    Capacity bound forest ↔ Domains.Capacity bound (domains forest) := by
  constructor
  · intro h keys member
    obtain ⟨tree, inForest, rfl⟩ := List.mem_map.mp member
    simpa only [length_inorder] using h tree inForest
  · intro h tree member
    have bound := h (inorder tree) (List.mem_map.mpr ⟨tree, member, rfl⟩)
    simpa only [length_inorder] using bound

/-- Only the prescribed join domains need a new size check. All other
operations preserve or decrease component size, independent of tree shape. -/
theorem Trace.capacity {access : Access α} {prepare : Preparation α}
    (accessKeeps : AccessPreserves access) (prepareKeeps : PreparationPreserves prepare)
    {a b : List (RawTree α)} {word : List (Event α)} {work bound : Nat}
    (run : Trace access prepare a word b work) (initial : Capacity bound a)
    (joins : ∀ event ∈ word, Domains.JoinFits bound event) : Capacity bound b := by
  exact (capacity_iff_domains bound b).mpr
    ((Trace.toDomains accessKeeps prepareKeeps run).capacity
      ((capacity_iff_domains bound a).mp initial) joins)

end MultiSplay.CommonForest

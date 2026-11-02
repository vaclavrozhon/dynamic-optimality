import ChaCha.Entropy.ExpectationUniform
import DynamicOptimality.Funnel.AdjacentPairs

/-!
# The actual local token order under a random permutation

Restriction keeps exactly the occurrence tokens belonging to one auxiliary
interval. Its adjacency pairs are a path on those tokens, so their number is
one less than the interval multiplicity. Relabelling the tokens commutes
with restriction whenever it preserves the interval.
-/

namespace ChaCha.Entropy

open scoped BigOperators
open DynamicOptimality.Funnel (descendingPairs descendingPairs_mem descendingPairs_nodup)

variable {m : Nat}

def localOrder (sample : Equiv.Perm (Fin m)) (active : Finset (Fin m)) : List (Fin m) :=
  ((List.finRange m).map sample).filter (fun token => decide (token ∈ active))

@[simp] theorem mem_localOrder (sample : Equiv.Perm (Fin m)) (active : Finset (Fin m)) (token : Fin m) :
    token ∈ localOrder sample active ↔ token ∈ active := by
  simp only [localOrder,List.mem_filter,decide_eq_true_eq]
  rw [sample.map_finRange_perm.mem_iff]
  simp

theorem localOrder_nodup (sample : Equiv.Perm (Fin m)) (active : Finset (Fin m)) :
    (localOrder sample active).Nodup :=
  ((List.nodup_finRange m).map sample.injective).filter _

@[simp] theorem localOrder_toFinset (sample : Equiv.Perm (Fin m)) (active : Finset (Fin m)) :
    (localOrder sample active).toFinset = active := by
  ext token
  simp only [List.mem_toFinset,mem_localOrder]

@[simp] theorem localOrder_length (sample : Equiv.Perm (Fin m)) (active : Finset (Fin m)) :
    (localOrder sample active).length = active.card := by
  rw [← List.toFinset_card_of_nodup (localOrder_nodup sample active),localOrder_toFinset]

theorem descendingPairs_length {α : Type*} (word : List α) :
    (descendingPairs word).length = word.length - 1 := by
  induction word with
  | nil => rfl
  | cons a word ih =>
    cases word with
    | nil => rfl
    | cons b word => simp only [descendingPairs,List.length_cons] at ih ⊢; omega

theorem descendingPairs_no_loop {α : Type*} {word : List α} (nodup : word.Nodup) (a : α) :
    (a,a) ∉ descendingPairs word := by
  induction word with
  | nil => simp [descendingPairs]
  | cons b word ih =>
    obtain ⟨absent,tail⟩ := List.nodup_cons.mp nodup
    cases word with
    | nil => simp [descendingPairs]
    | cons c word =>
      intro member
      simp only [descendingPairs,List.mem_cons,Prod.mk.injEq] at member
      rcases member with ⟨rfl,rfl⟩ | member
      · exact absent List.mem_cons_self
      · exact ih tail member

theorem descendingPairs_map {α β : Type*} (f : α → β) (word : List α) :
    descendingPairs (word.map f) = (descendingPairs word).map (fun pair => (f pair.1,f pair.2)) := by
  induction word with
  | nil => rfl
  | cons a word ih =>
    cases word with
    | nil => rfl
    | cons b word => simpa only [List.map_cons,descendingPairs] using congrArg (List.cons (f b,f a)) ih

theorem descendingPairs_alternations {α β : Type*} [DecidableEq β] (label : α → β) (word : List α) :
    ((descendingPairs word).filter (fun pair => decide (label pair.1 ≠ label pair.2))).length =
      ChaCha.alternations (word.map label) := by
  induction word with
  | nil => rfl
  | cons a word ih =>
    cases word with
    | nil => rfl
    | cons b word =>
      by_cases same : label a = label b
      · simpa [descendingPairs,ChaCha.alternations_cons_cons,same,ChaCha.edgeChange] using ih
      · have reverse : label b ≠ label a := Ne.symm same
        simpa [descendingPairs,reverse,same,ChaCha.edgeChange,
          ChaCha.alternations_cons_cons,Nat.add_comm] using congrArg Nat.succ ih

theorem localOrder_relabel (sample rename : Equiv.Perm (Fin m)) (active : Finset (Fin m))
    (preserves : ∀ token, rename token ∈ active ↔ token ∈ active) :
    localOrder (sample.trans rename) active = (localOrder sample active).map rename := by
  have predicate : (fun token => decide (token ∈ active)) ∘ rename =
      (fun token => decide (token ∈ active)) := by funext token; simp [preserves]
  unfold localOrder
  change ((List.finRange m).map (rename ∘ sample)).filter _ = _
  rw [← List.map_map,List.filter_map,predicate]

/-- Reindexing the uniform permutation sample by a fixed token relabelling. -/
def relabelSamples (rename : Equiv.Perm (Fin m)) :
    Equiv.Perm (Equiv.Perm (Fin m)) where
  toFun sample := sample.trans rename
  invFun sample := sample.trans rename.symm
  left_inv sample := by ext token; simp
  right_inv sample := by ext token; simp

def adjacency (sample : Equiv.Perm (Fin m)) (active : Finset (Fin m)) (p q : Fin m) : ℝ :=
  if (p,q) ∈ descendingPairs (localOrder sample active) then 1 else 0

@[simp] theorem adjacency_self (sample : Equiv.Perm (Fin m)) (active : Finset (Fin m)) (p : Fin m) :
    adjacency sample active p p = 0 := by
  simp only [adjacency,if_neg (descendingPairs_no_loop (localOrder_nodup sample active) p)]

theorem adjacency_relabel (sample rename : Equiv.Perm (Fin m)) (active : Finset (Fin m))
    (preserves : ∀ token, rename token ∈ active ↔ token ∈ active) (p q : Fin m) :
    adjacency (sample.trans rename) active (rename p) (rename q) = adjacency sample active p q := by
  unfold adjacency
  rw [localOrder_relabel sample rename active preserves,descendingPairs_map]
  congr 1
  simp only [List.mem_map,Prod.exists,Prod.mk.injEq,rename.injective.eq_iff]
  simp

theorem adjacency_sum (sample : Equiv.Perm (Fin m)) (active : Finset (Fin m)) :
    (∑ p ∈ active, ∑ q ∈ active, adjacency sample active p q) = (active.card - 1 : Nat) := by
  let pairs := (descendingPairs (localOrder sample active)).toFinset
  have contained : pairs ⊆ active ×ˢ active := by
    intro pair member
    have both := descendingPairs_mem (List.mem_toFinset.mp member)
    exact Finset.mem_product.mpr ⟨(mem_localOrder _ _ _).mp both.1,(mem_localOrder _ _ _).mp both.2⟩
  have filtered' : (active ×ˢ active).filter (fun pair => pair ∈ pairs) = pairs := by
    ext pair
    simp only [Finset.mem_filter]
    exact ⟨And.right,fun member => ⟨contained member,member⟩⟩
  have length := descendingPairs_length (localOrder sample active)
  have count : pairs.card = active.card - 1 := by
    rw [List.toFinset_card_of_nodup (descendingPairs_nodup _ (localOrder_nodup sample active)),
      length,localOrder_length]
  have natural : (∑ p ∈ active, ∑ q ∈ active,
      if (p,q) ∈ pairs then (1:Nat) else 0) = active.card - 1 := by
    rw [← Finset.sum_product active active (fun pair => if pair ∈ pairs then (1:Nat) else 0)]
    rw [← Finset.card_eq_sum_ite contained]
    exact count
  simpa only [adjacency,pairs,List.mem_toFinset] using (show
    (∑ p ∈ active, ∑ q ∈ active, if (p,q) ∈ pairs then (1:ℝ) else 0) = (active.card - 1 : Nat) by
      exact_mod_cast natural)

end ChaCha.Entropy

import MultiSplay.ForestSplayActions

/-!
# Removing administrative steps from physical splay traces

`SplayRun invariant` has exactly one action per event. Permutations and identity
preparations disappear without cost. The predicate `invariant` records only
properties of physical forests, independently of any amortized accounting.
-/

namespace MultiSplay.CommonForest

open DynamicOptimality (RawTree)
open TangoSquared.MTR.Tree (inorder)

variable {α : Type*}

inductive SplayRun (invariant : List (RawTree α) → Prop) :
    List (RawTree α) → List (Event α) → List (RawTree α) → Nat → Prop
  | done {before after : List (RawTree α)} (valid : invariant before) (same : before.Perm after) :
      SplayRun invariant before [] after 0
  | next {before middle after : List (RawTree α)} {event : Event α} {word : List (Event α)} {head tail : Nat}
      (valid : invariant before) (action : SplayAction event before middle head)
      (rest : SplayRun invariant middle word after tail) : SplayRun invariant before (event::word) after (head+tail)

theorem SplayRun.permute_source {invariant : List (RawTree α) → Prop}
    {before before' after : List (RawTree α)} {word : List (Event α)} {cost : Nat}
    (run : SplayRun invariant before word after cost) (order : before'.Perm before) (valid : invariant before') :
    SplayRun invariant before' word after cost := by
  cases run with
  | done _ same => exact .done valid (order.trans same)
  | next _ action rest => exact .next valid (action.permute order (List.Perm.refl _)) rest

theorem SplayRun.deterministic {invariant : List (RawTree α) → Prop}
    {before before' after after' : List (RawTree α)} {word : List (Event α)} {cost cost' : Nat}
    (first : SplayRun UniqueKeys before word after cost) (second : SplayRun invariant before' word after' cost')
    (order : before.Perm before') : after.Perm after' ∧ cost = cost' := by
  induction first generalizing before' after' cost' with
  | done unique same =>
      cases second with
      | done _ other => exact ⟨same.symm.trans (order.trans other), rfl⟩
  | next unique action rest ih =>
      cases second with
      | next _ other later =>
          obtain ⟨middle, headEq⟩ := action.deterministic other unique order
          obtain ⟨final, tailEq⟩ := ih later middle
          exact ⟨final, by omega⟩

theorem Step.splay_classify {before after : List (RawTree α)} {word : List (Event α)} {cost : Nat}
    (step : Step Auxiliary.Splay idle before word after cost) :
    (word = [] ∧ cost = 0 ∧ before.Perm after) ∨
      ∃ event, word = [event] ∧ SplayAction event before after cost := by
  induction step with
  | search execution =>
      exact .inr ⟨_, rfl, _, _, [], .search execution, List.Perm.refl _, List.Perm.refl _⟩
  | split execution =>
      exact .inr ⟨_, rfl, _, _, [], .split execution, List.Perm.refl _, List.Perm.refl _⟩
  | join left right pivot =>
      exact .inr ⟨_, rfl, _, _, [], .join left right pivot, List.Perm.refl _, List.Perm.refl _⟩
  | prepare execution =>
      obtain ⟨rfl, rfl⟩ := execution
      exact .inl ⟨rfl,rfl,List.Perm.refl _⟩
  | context step front back ih =>
      rcases ih with ⟨empty, zero, order⟩ | ⟨event, wordEq, action⟩
      · exact .inl ⟨empty,zero,(order.append_left front).append_right back⟩
      · exact .inr ⟨event,wordEq,action.context front back⟩
  | reorder order => exact .inl ⟨rfl,rfl,order⟩

theorem SplayTrace.toRun {before after : List (RawTree α)} {word : List (Event α)} {cost : Nat}
    (trace : SplayTrace before word after cost) : SplayRun (fun _ => True) before word after cost := by
  induction trace with
  | nil => exact .done trivial (List.Perm.refl _)
  | cons step rest ih =>
      rcases step.splay_classify with ⟨rfl,rfl,order⟩ | ⟨event,rfl,action⟩
      · simpa only [List.nil_append, Nat.zero_add] using ih.permute_source order trivial
      · exact .next trivial action ih

/-- An actual physical splay trace with distinct keys at each checkpoint.
This is a tree-validity condition, with no cost or accounting hypotheses. -/
inductive DistinctSplayTrace : List (RawTree α) → List (Event α) → List (RawTree α) → Nat → Prop
  | nil (forest : List (RawTree α)) (unique : UniqueKeys forest) : DistinctSplayTrace forest [] forest 0
  | cons {before middle after : List (RawTree α)} {first rest : List (Event α)} {head tail : Nat}
      (unique : UniqueKeys before) (step : Step Auxiliary.Splay idle before first middle head)
      (remaining : DistinctSplayTrace middle rest after tail) :
      DistinctSplayTrace before (first++rest) after (head+tail)

theorem DistinctSplayTrace.toSplay {before after : List (RawTree α)} {word : List (Event α)} {cost : Nat}
    (trace : DistinctSplayTrace before word after cost) : SplayTrace before word after cost := by
  induction trace with
  | nil => exact .nil _
  | cons unique step remaining ih => exact .cons step ih

theorem DistinctSplayTrace.toRun {before after : List (RawTree α)} {word : List (Event α)} {cost : Nat}
    (trace : DistinctSplayTrace before word after cost) : SplayRun UniqueKeys before word after cost := by
  induction trace with
  | nil forest unique => exact .done unique (List.Perm.refl _)
  | cons unique step rest ih =>
      rcases step.splay_classify with ⟨rfl,rfl,order⟩ | ⟨event,rfl,action⟩
      · simpa only [List.nil_append, Nat.zero_add] using ih.permute_source order unique
      · exact .next unique action ih

/-- Any other realization of the same common word from the same physical
forest has the same cost and the same final trees, up to list permutation. -/
theorem DistinctSplayTrace.deterministic {before before' after after' : List (RawTree α)}
    {word : List (Event α)} {cost cost' : Nat}
    (first : DistinctSplayTrace before word after cost) (second : SplayTrace before' word after' cost')
    (same : before.Perm before') : after.Perm after' ∧ cost = cost' :=
  first.toRun.deterministic second.toRun same

end MultiSplay.CommonForest

import TangoSquared.Paper20261030.PredicateSearch
import TangoSquared.Paper20261030.DepthPreferences
import TangoSquared.Paper20261030.ReferenceHeight

/-!
# Concrete interval records along a secondary preferred path

A core record stores an actual depth-reference split and its preference
bit. Its key is the vertex's reference depth. The records on a preferred
path have increasing keys and nested intervals. Interval containment is
therefore a prefix predicate, so the observed binary search finds the
deepest containing interval in any balanced auxiliary tree representing
this exact record word.

These statements concern an unpruned depth reference. Maintaining the
balanced representation and treating completed/dormant restrictions are
separate obligations.
-/

namespace TangoSquared.Paper20261030.SecondaryCore

open Std.DTreeMap.Internal Std.DTreeMap.Internal.Impl
open RouterProjection
open Auxiliary Auxiliary.Metadata

abbrev Record := DepthSplit × Bool
abbrev Entry := Sigma (fun _ : Nat => Record)

def word (start : Nat) : {a b : Nat} → DepthTree a b → (DepthSplit → Bool) → List Entry
  | _,_,.leaf _,_ => []
  | a,b,.node cut _ _ l r,preference =>
    ⟨start,(⟨a,cut,b⟩,preference ⟨a,cut,b⟩)⟩ ::
      if preference ⟨a,cut,b⟩ then word (start + 1) r preference
      else word (start + 1) l preference

theorem mem_word (start : Nat) {a b : Nat} (reference : DepthTree a b)
    (preference : DepthSplit → Bool) {entry : Entry} (he : entry ∈ word start reference preference) :
    entry.2.1 ∈ reference.nodes ∧ start ≤ entry.1 := by
  induction reference generalizing start with
  | leaf => simp [word] at he
  | @node a b cut ha hb l r ihl ihr =>
    simp only [word,List.mem_cons] at he
    rcases he with rfl | he
    · exact ⟨by simp [DepthTree.nodes],le_rfl⟩
    · split at he
      · obtain ⟨hm,hd⟩ := ihr (start + 1) he
        exact ⟨by simp [DepthTree.nodes,hm],by omega⟩
      · obtain ⟨hm,hd⟩ := ihl (start + 1) he
        exact ⟨by simp [DepthTree.nodes,hm],by omega⟩

theorem keys_increasing (start : Nat) {a b : Nat} (reference : DepthTree a b)
    (preference : DepthSplit → Bool) : (word start reference preference).Pairwise (fun e f => e.1 < f.1) := by
  induction reference generalizing start with
  | leaf => exact .nil
  | @node a b cut ha hb l r ihl ihr =>
    simp only [word]
    split
    · apply List.pairwise_cons.mpr
      exact ⟨fun e he => by change start < e.1; have := (mem_word (start + 1) r preference he).2; omega,ihr _⟩
    · apply List.pairwise_cons.mpr
      exact ⟨fun e he => by change start < e.1; have := (mem_word (start + 1) l preference he).2; omega,ihl _⟩

theorem intervals_nested (start : Nat) {a b : Nat} (reference : DepthTree a b)
    (preference : DepthSplit → Bool) :
    (word start reference preference).Pairwise (fun e f => e.2.1.lo ≤ f.2.1.lo ∧ f.2.1.hi ≤ e.2.1.hi) := by
  induction reference generalizing start with
  | leaf => exact .nil
  | @node a b cut ha hb l r ihl ihr =>
    simp only [word]
    split
    · apply List.pairwise_cons.mpr
      refine ⟨?_,ihr _⟩
      intro entry he
      have bounds := r.node_bounds (mem_word (start + 1) r preference he).1
      change a ≤ entry.2.1.lo ∧ entry.2.1.hi ≤ b
      omega
    · apply List.pairwise_cons.mpr
      refine ⟨?_,ihl _⟩
      intro entry he
      have bounds := l.node_bounds (mem_word (start + 1) l preference he).1
      change a ≤ entry.2.1.lo ∧ entry.2.1.hi ≤ b
      omega

def containsDepth (d : Nat) (entry : Entry) : Bool :=
  decide (entry.2.1.lo ≤ d ∧ d ≤ entry.2.1.hi)

theorem containment_prefix (d start : Nat) {a b : Nat} (reference : DepthTree a b)
    (preference : DepthSplit → Bool) :
    (word start reference preference).Pairwise
      (fun e f => containsDepth d f = true → containsDepth d e = true) := by
  apply (intervals_nested start reference preference).imp
  intro e f hn hf
  simp only [containsDepth,decide_eq_true_eq] at hf ⊢
  omega

theorem word_length (start : Nat) {a b : Nat} (reference : DepthTree a b)
    (preference : DepthSplit → Bool) :
    (word start reference preference).length ≤ (LocalReferences.depthReference reference).height := by
  induction reference generalizing start with
  | leaf => exact le_rfl
  | @node a b cut ha hb l r ihl ihr =>
    simp only [word,List.length_cons,LocalReferences.depthReference,Router.height]
    split
    · have := ihr (start + 1); omega
    · have := ihl (start + 1); omega

theorem core_search_correct (d start : Nat) {a b : Nat} (reference : DepthTree a b)
    (preference : DepthSplit → Bool) (core : Impl Nat (fun _ => Record))
    (hword : core.toListModel = word start reference preference) :
    lastGood (containsDepth d) core =
      ((word start reference preference).filter (containsDepth d)).getLast? := by
  rw [← hword]
  apply lastGood_correct
  change core.toListModel.Pairwise _
  rw [hword]
  exact containment_prefix d start reference preference

theorem core_search_charged (d start : Nat) {a b : Nat} (reference : DepthTree a b)
    (preference : DepthSplit → Bool) (core : Impl Nat (fun _ => Record))
    (hb : core.Balanced) (hword : core.toListModel = word start reference preference) (ancestors) :
    ∃ cost, Trace ⟨recordTree core,ancestors⟩ (queryReads (containsDepth d) core)
      ⟨recordTree core,ancestors⟩ cost ∧
      cost ≤ 9 * Nat.clog 2 ((LocalReferences.depthReference reference).height + 1) := by
  have hsize : core.size ≤ (LocalReferences.depthReference reference).height := by
    rw [size_eq_length core hb,hword]
    exact word_length start reference preference
  obtain ⟨cost,trace,hcost⟩ := query_charged_log (containsDepth d) core hb ancestors
  have hm := Nat.clog_monotone 2 (Nat.add_le_add_right hsize 1)
  exact ⟨cost,trace,by omega⟩

end TangoSquared.Paper20261030.SecondaryCore

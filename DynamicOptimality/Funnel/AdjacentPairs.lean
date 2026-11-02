import DynamicOptimality.Funnel.Alternation
import Mathlib.Data.List.Pairwise
import Mathlib.Data.Finset.Card

/-! # Adjacent pairs in a strictly decreasing occurrence list -/

namespace DynamicOptimality.Funnel

variable {τ β : Type*}

/-- Pairs are stored as (older, newer), although the list runs newest first. -/
def descendingPairs : List τ → List (τ × τ)
  | [] => []
  | [_] => []
  | a :: b :: rest => (b,a) :: descendingPairs (b :: rest)

theorem descendingPairs_mem {word : List τ} {q r : τ}
    (member : (q,r) ∈ descendingPairs word) : q ∈ word ∧ r ∈ word := by
  induction word with
  | nil => simp [descendingPairs] at member
  | cons a word ih =>
    cases word with
    | nil => simp [descendingPairs] at member
    | cons b word =>
      simp only [descendingPairs,List.mem_cons,Prod.mk.injEq] at member
      rcases member with ⟨rfl,rfl⟩ | member
      · simp
      · obtain ⟨hq,hr⟩ := ih member
        exact ⟨List.mem_cons_of_mem _ hq,List.mem_cons_of_mem _ hr⟩

theorem descendingPairs_nodup [DecidableEq τ] (word : List τ) (nodup : word.Nodup) :
    (descendingPairs word).Nodup := by
  induction word with
  | nil => simp [descendingPairs]
  | cons a word ih =>
    obtain ⟨absent,tail⟩ := List.nodup_cons.mp nodup
    cases word with
    | nil => simp [descendingPairs]
    | cons b word =>
      simp only [descendingPairs,List.nodup_cons]
      exact ⟨fun member => absent (descendingPairs_mem member).2,ih tail⟩

theorem descendingPairs_iff [LinearOrder τ] (word : List τ)
    (sorted : word.Pairwise (fun a b => b < a)) (q r : τ) :
    (q,r) ∈ descendingPairs word ↔ q ∈ word ∧ r ∈ word ∧ q < r ∧
      ∀ s ∈ word, q < s → s < r → False := by
  induction word with
  | nil => simp [descendingPairs]
  | cons a word ih =>
    obtain ⟨largest,tailSorted⟩ := List.pairwise_cons.mp sorted
    cases word with
    | nil =>
      simp only [descendingPairs,List.not_mem_nil,false_iff,List.mem_singleton]
      rintro ⟨rfl,rfl,strict,_⟩
      exact lt_irrefl _ strict
    | cons b word =>
      have ba := largest b List.mem_cons_self
      obtain ⟨second,restSorted⟩ := List.pairwise_cons.mp tailSorted
      simp only [descendingPairs,List.mem_cons,Prod.mk.injEq]
      constructor
      · rintro (⟨rfl,rfl⟩ | member)
        · refine ⟨Or.inr (Or.inl rfl),Or.inl rfl,ba,?_⟩
          intro s hs bs sa
          rcases hs with rfl | rfl | hs
          · exact lt_irrefl _ sa
          · exact lt_irrefl _ bs
          · exact lt_asymm bs (second s hs)
        · obtain ⟨hq,hr,qr,empty⟩ := (ih tailSorted).mp member
          refine ⟨Or.inr (List.mem_cons.mp hq),Or.inr (List.mem_cons.mp hr),qr,?_⟩
          intro s hs qs sr
          rcases hs with rfl | hs
          · exact lt_asymm sr (largest r hr)
          · exact empty s (List.mem_cons.mpr hs) qs sr
      · rintro ⟨hq,hr,qr,empty⟩
        rcases hr with rfl | hr
        · rcases hq with rfl | rfl | hq
          · exact (lt_irrefl _ qr).elim
          · exact Or.inl ⟨rfl,rfl⟩
          · exact (empty b (Or.inr (Or.inl rfl)) (second q hq) ba).elim
        · have rIn : r ∈ b :: word := List.mem_cons.mpr hr
          have qa : q ≠ a := fun same => lt_asymm (same ▸ qr) (largest r rIn)
          have qIn : q ∈ b :: word := by
            rcases hq with same | hq
            · exact (qa same).elim
            · exact List.mem_cons.mpr hq
          refine Or.inr ((ih tailSorted).mpr ⟨qIn,rIn,qr,?_⟩)
          intro s hs qs sr
          exact empty s (Or.inr (List.mem_cons.mp hs)) qs sr

theorem descendingPairs_changes [DecidableEq β] (label : τ → β) (word : List τ) :
    ((descendingPairs word).filter (fun pair => decide (label pair.1 ≠ label pair.2))).length =
      changes (word.map label) := by
  induction word with
  | nil => rfl
  | cons a word ih =>
    cases word with
    | nil => simp [descendingPairs,changes,changesFrom,changeStep]
    | cons b word =>
      simp only [descendingPairs,List.filter_cons]
      by_cases same : label a = label b
      · simpa [changes,changesFrom,changeStep,same] using ih
      · have reverse : label b ≠ label a := Ne.symm same
        simp [same,reverse,List.length_cons,ih,changes,changesFrom,changeStep,Nat.add_comm]
        simpa [changes,changesFrom,changeStep] using ih

end DynamicOptimality.Funnel

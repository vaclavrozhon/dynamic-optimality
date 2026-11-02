import ChaCha.Entropy.OrderedReference
import ChaCha.Paper20261030.FragmentDecomposition
import Mathlib.Data.Multiset.UnionInter

/-!
# Actual event multiplicities at original request times

A multiset of integer timestamps retains one copy for every counted
event. Different vertices can contribute at the same request. Projection
changes only keys, so all recursively collected timestamps remain in the
original time coordinate system. The cardinality theorems identify these
profiles with the repository's primary and fragment counters exactly.
-/

namespace ChaCha.Entropy

open PreferredProjection Paper20261030 Paper20261030.Dyadic Paper20261030.Rectangles Secondary
open scoped BigOperators
attribute [local instance] Classical.propDecidable

noncomputable def eventTimes (points : Finset Point) (event : Point → Prop) : Multiset Int :=
  (points.filter event).val.map Prod.snd

theorem eventTimes_card (points : Finset Point) (event : Point → Prop) :
    (eventTimes points event).card = eventCount points event := by
  rw [eventCount_eq_card]
  simp only [eventTimes,Multiset.card_map,Finset.card]

def branchProjection (left : List Int) (key : Int) : Int := if key ∈ left then 0 else 1

theorem branchWord_projection (left right word : List Int)
    (keys : ∀ key ∈ word, key ∈ left ++ right) :
    (PrefRouter.branchWord left right word).map (branchIndex 0) = word.map (branchProjection left) := by
  induction word with
  | nil => rfl
  | cons key word ih =>
      have rest := ih (fun other present => keys other (by simp [present]))
      by_cases low : key ∈ left
      · simp [PrefRouter.branchWord,branchProjection,low,branchIndex]
        exact rest
      · have high := (List.mem_append.mp (keys key (by simp))).resolve_left low
        simp [PrefRouter.branchWord,branchProjection,low,high,branchIndex]
        exact rest

theorem branch_switch_count (left right : List Int) (points : List Point)
    (chronological : Chronological points) (keys : ∀ point ∈ points, point.1 ∈ left ++ right) :
    switchCount (project (branchProjection left) points.toFinset) =
      alternations (PrefRouter.branchWord left right (points.map Prod.fst)) := by
  have bound := alternations_switchCount (points.map (mapPoint (branchProjection left)))
    (chronological_project chronological _)
  have mapped : (points.map (mapPoint (branchProjection left))).toFinset =
      project (branchProjection left) points.toFinset := by ext point; simp [project]
  have words : (points.map (mapPoint (branchProjection left))).map Prod.fst =
      (points.map Prod.fst).map (branchProjection left) := by simp only [List.map_map]; rfl
  have branch := branchWord_projection left right (points.map Prod.fst) (by
    intro key member
    obtain ⟨point,present,rfl⟩ := List.mem_map.mp member
    exact keys point present)
  rw [mapped,words,← branch,alternations_injective_map _ (branchIndex_injective 0)] at bound
  exact bound.symm

noncomputable def primaryEvents : PrefRouter Int → List Point → Multiset Int
  | .leaf _, _ => 0
  | .fork _ left right, points =>
      let projected := project (branchProjection left.leaves) points.toFinset
      eventTimes projected (SwitchPoint projected) +
        primaryEvents left (points.filter (fun point => decide (point.1 ∈ left.leaves))) +
        primaryEvents right (points.filter (fun point => decide (point.1 ∉ left.leaves ∧ point.1 ∈ right.leaves)))

theorem primaryEvents_card (reference : PrefRouter Int) (points : List Point)
    (chronological : Chronological points) (keys : ∀ point ∈ points, point.1 ∈ reference.leaves) :
    (primaryEvents reference points).card = reference.primaryWilber (points.map Prod.fst) := by
  induction reference generalizing points with
  | leaf => rfl
  | fork preference left right ihl ihr =>
      have low := ihl (points.filter (fun point => decide (point.1 ∈ left.leaves)))
        (chronological_filter chronological _) (by
          intro point member
          exact of_decide_eq_true (List.mem_filter.mp member).2)
      have high := ihr (points.filter (fun point => decide (point.1 ∉ left.leaves ∧ point.1 ∈ right.leaves)))
        (chronological_filter chronological _) (by
          intro point member
          exact (of_decide_eq_true (List.mem_filter.mp member).2).2)
      have switches := branch_switch_count _ _ points chronological keys
      change eventCount _ (SwitchPoint _) = _ at switches
      simp only [primaryEvents,Multiset.card_add,eventTimes_card,low,high,PrefRouter.primaryWilber]
      rw [switches]
      rw [keys_filter_points points (fun key => decide (key ∈ left.leaves)),
        keys_filter_points points (fun key => decide (key ∉ left.leaves ∧ key ∈ right.leaves))]
      rfl

noncomputable def fragmentEvents : {a b : Nat} → DepthTree a b → Finset Point → Multiset Int
  | _,_,.leaf _,_ => 0
  | _,b,.node cut _ _ left right,points =>
      let projection := coarsen (b+1) (cut+1)
      eventTimes points (DownUpAt points projection) +
        fragmentEvents left (project projection points) +
        ∑ index ∈ points.image (fun point => projection point.1),
          fragmentEvents right (fiber projection index points)

theorem fragmentEvents_card {a b : Nat} (reference : DepthTree a b) (points : Finset Point) :
    (fragmentEvents reference points).card = fragmentAlternations reference points := by
  induction reference generalizing points with
  | leaf => rfl
  | node cut lower upper left right ihl ihr =>
      simp only [fragmentEvents,Multiset.card_add,eventTimes_card,Multiset.card_sum,
        ihl,ihr,fragmentAlternations]

end ChaCha.Entropy

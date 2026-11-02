import ChaCha.Entropy.EventProfiles
import ChaCha.Paper20261030.RobustCountingBound
import ChaCha.Paper20261030.SharedOPTBound

/-!
# The residual alternation lower bound

The original primary and depth references remain fixed. At each original
time, auxiliary-reference events are retained only beyond the number of
events already counted there. Multiset subtraction implements this exact
per-time deficit. The result dominates both original counters together
and the auxiliary reference, while remaining bounded by the shared OPT.
-/

namespace ChaCha.Entropy

open PreferredProjection Paper20261030 Paper20261030.Dyadic Paper20261030.Rectangles
open scoped BigOperators

noncomputable def baselineEvents {a b : Nat} (primary : PrefRouter Int) (depth : DepthTree a b)
    (requests : List Int) : Multiset Int :=
  primaryEvents primary (pointWord 0 requests) + fragmentEvents depth (accessPoints requests)

noncomputable def auxiliaryEvents (auxiliary : PrefRouter Int) (requests : List Int) : Multiset Int :=
  primaryEvents auxiliary (pointWord 0 requests)

noncomputable def residualEvents {a b : Nat} (primary : PrefRouter Int) (depth : DepthTree a b)
    (auxiliary : PrefRouter Int) (requests : List Int) : Multiset Int :=
  auxiliaryEvents auxiliary requests - baselineEvents primary depth requests

noncomputable def residualBound {a b : Nat} (primary : PrefRouter Int) (depth : DepthTree a b)
    (auxiliary : PrefRouter Int) (requests : List Int) : Nat :=
  requests.length + (auxiliaryEvents auxiliary requests ∪ baselineEvents primary depth requests).card

theorem request_primaryEvents_card (reference : PrefRouter Int) (requests : List Int)
    (keys : ∀ key ∈ requests, key ∈ reference.leaves) :
    (primaryEvents reference (pointWord 0 requests)).card = reference.primaryWilber requests := by
  have bound := primaryEvents_card reference (pointWord 0 requests) (pointWord_chronological 0 requests) (by
    intro point member
    have present : point.1 ∈ (pointWord 0 requests).map Prod.fst := List.mem_map.mpr ⟨point,member,rfl⟩
    rw [pointWord_keys] at present
    exact keys point.1 present)
  simpa only [pointWord_keys] using bound

theorem baselineEvents_card {a b : Nat} (primary : PrefRouter Int) (depth : DepthTree a b)
    (requests : List Int) (keys : ∀ key ∈ requests, key ∈ primary.leaves) :
    (baselineEvents primary depth requests).card =
      primary.primaryWilber requests + fragmentAlternations depth (accessPoints requests) := by
  simp only [baselineEvents,Multiset.card_add,request_primaryEvents_card primary requests keys,fragmentEvents_card]

theorem residual_count {a b : Nat} (primary : PrefRouter Int) (depth : DepthTree a b)
    (auxiliary : PrefRouter Int) (requests : List Int) (time : Int) :
    (residualEvents primary depth auxiliary requests).count time =
      (auxiliaryEvents auxiliary requests).count time - (baselineEvents primary depth requests).count time :=
  Multiset.count_sub _ _ _

theorem residual_identity {a b : Nat} (primary : PrefRouter Int) (depth : DepthTree a b)
    (auxiliary : PrefRouter Int) (requests : List Int)
    (keys : ∀ key ∈ requests, key ∈ primary.leaves) :
    residualBound primary depth auxiliary requests =
      requests.length + primary.primaryWilber requests + fragmentAlternations depth (accessPoints requests) +
        (residualEvents primary depth auxiliary requests).card := by
  unfold residualBound
  rw [Multiset.union_def,Multiset.card_add,baselineEvents_card primary depth requests keys]
  change _ = _ + (auxiliaryEvents auxiliary requests - baselineEvents primary depth requests).card
  omega

theorem residual_domination {a b : Nat} (primary : PrefRouter Int) (depth : DepthTree a b)
    (auxiliary : PrefRouter Int) (requests : List Int)
    (primaryKeys : ∀ key ∈ requests, key ∈ primary.leaves)
    (auxiliaryKeys : ∀ key ∈ requests, key ∈ auxiliary.leaves) :
    max (requests.length + primary.primaryWilber requests + fragmentAlternations depth (accessPoints requests))
      (requests.length + auxiliary.primaryWilber requests) ≤ residualBound primary depth auxiliary requests := by
  have baseline := Multiset.card_le_card (Multiset.le_union_right (s := auxiliaryEvents auxiliary requests)
    (t := baselineEvents primary depth requests))
  have auxiliaryBound := Multiset.card_le_card (Multiset.le_union_left (s := auxiliaryEvents auxiliary requests)
    (t := baselineEvents primary depth requests))
  rw [baselineEvents_card primary depth requests primaryKeys] at baseline
  have auxiliaryCard : (auxiliaryEvents auxiliary requests).card = auxiliary.primaryWilber requests :=
    request_primaryEvents_card auxiliary requests auxiliaryKeys
  rw [auxiliaryCard] at auxiliaryBound
  unfold residualBound
  apply max_le
  · omega
  · exact Nat.add_le_add_left auxiliaryBound _

theorem residual_robust_bound {a b : Nat} (primary : PrefRouter Int) (depth : DepthTree a b)
    (auxiliary : PrefRouter Int) (requests : List Int)
    (primaryOrdered : primary.leaves.Pairwise (· < ·)) (auxiliaryOrdered : auxiliary.leaves.Pairwise (· < ·))
    (primaryKeys : ∀ key ∈ requests, key ∈ primary.leaves)
    (auxiliaryKeys : ∀ key ∈ requests, key ∈ auxiliary.leaves) :
    residualBound primary depth auxiliary requests ≤ requests.length + 7*robustBound (accessPoints requests) := by
  have first := ordered_reference_robust primary primaryOrdered requests primaryKeys
  have second := ordered_reference_robust auxiliary auxiliaryOrdered requests auxiliaryKeys
  have fragments := (fragmentDecomposition depth (accessPoints requests)).alternations_le_robustBound
    (accessPoints_instance requests)
  rw [← fragmentAlternations_eq_decomposition depth (accessPoints_instance requests)] at fragments
  have remaining := Multiset.card_le_card
    (Multiset.sub_le_self (auxiliaryEvents auxiliary requests) (baselineEvents primary depth requests))
  rw [auxiliaryEvents,request_primaryEvents_card auxiliary requests auxiliaryKeys] at remaining
  rw [residual_identity primary depth auxiliary requests primaryKeys]
  change (residualEvents primary depth auxiliary requests).card ≤ auxiliary.primaryWilber requests at remaining
  omega

theorem residual_shared_OPT {n a b : Nat} (primary : PrefRouter Int) (depth : DepthTree a b)
    (auxiliary : PrefRouter Int) (requests : List (Fin n))
    (primaryOrdered : primary.leaves.Pairwise (· < ·)) (auxiliaryOrdered : auxiliary.leaves.Pairwise (· < ·))
    (primaryKeys : ∀ key ∈ requests, (key.val:Int) ∈ primary.leaves)
    (auxiliaryKeys : ∀ key ∈ requests, (key.val:Int) ∈ auxiliary.leaves) :
    residualBound primary depth auxiliary (requests.map (fun key => (key.val:Int))) ≤
      519*DynamicOptimality.OPT requests := by
  have bound := residual_robust_bound primary depth auxiliary (requests.map (fun key => (key.val:Int)))
    primaryOrdered auxiliaryOrdered (by
      intro key member
      obtain ⟨original,present,rfl⟩ := List.mem_map.mp member
      exact primaryKeys original present) (by
      intro key member
      obtain ⟨original,present,rfl⟩ := List.mem_map.mp member
      exact auxiliaryKeys original present)
  have rectangles := robustBound_le_shared_OPT requests
  obtain ⟨_,_,_,_,cost⟩ := DynamicOptimality.OPT_attained requests
  simp only [List.length_map] at bound
  omega

end ChaCha.Entropy

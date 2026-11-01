import MultiSplay.EndpointEncoding
import TangoSquared.Monotonicity
import TangoSquared.FlipAccounting
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-!
# The initialized primary counter for node queries

`nodeCost` includes every ancestor preference change and every mandatory final
toggle. Its exact row-by-row identity below uses the core owners in the encoded
leaf history. This charges initialization only once per original reference
node, even though the full leaf reference has height twice as large.
-/

namespace MultiSplay.EndpointEncoding

open TangoSquared (changesFrom edgeChange alternations primaryCount primaryAlternations)
open TangoSquared.Primary (Key branch owners mem_owners)

theorem nodeCost_eq_sum (height : Nat) (state : State) (addresses : List Key) :
    nodeCost height state addresses =
      ∑ owner ∈ owners height,
        changesFrom (state owner) ((encode height state addresses).filterMap (branch (core owner))) := by
  induction addresses generalizing state with
  | nil => simp [nodeCost, encode]
  | cons address rest ih =>
      rw [nodeCost, ih, nodeSwitches, Finset.card_filter, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro owner member
      simp only [encode, List.filterMap_cons, writes_match]
      cases write : nodeWrite state address owner with
      | none => simp [write, changes, nodeStep]
      | some b =>
          by_cases same : state owner = b <;>
            simp [write, changes, nodeStep, changesFrom, edgeChange, same]

theorem core_owners_subset (height : Nat) :
    (owners height).image core ⊆ owners (2 * height) := by
  intro owner member
  obtain ⟨address, inside, rfl⟩ := Finset.mem_image.mp member
  rw [mem_owners] at inside ⊢
  rw [core_length]
  omega

/-- Initialization is charged on the original core owners, not on every
node of the much larger doubled-height leaf reference. -/
theorem nodeCost_le_primary_add_nodes (height : Nat) (state : State) (addresses : List Key) :
    nodeCost height state addresses ≤
      primaryCount (2 * height) (encode height state addresses) + (owners height).card := by
  rw [nodeCost_eq_sum]
  have initialized := Finset.sum_le_sum (s := owners height)
    (fun owner _ => TangoSquared.FlipAccounting.changesFrom_le_alternations_add_one
      (state owner) ((encode height state addresses).filterMap (branch (core owner))))
  have coreBound :
      (∑ owner ∈ owners height,
        alternations ((encode height state addresses).filterMap (branch (core owner)))) ≤
        primaryCount (2 * height) (encode height state addresses) := by
    rw [← Finset.sum_image (f := fun owner =>
      alternations ((encode height state addresses).filterMap (branch owner)))
      (fun a _ b _ same => core_injective same)]
    exact Finset.sum_le_sum_of_subset (core_owners_subset height)
  simp only [Finset.sum_add_distrib, Finset.sum_const, Nat.nsmul_eq_mul, Nat.mul_one] at initialized
  omega

theorem owners_card_add_one (height : Nat) : (owners height).card + 1 = 2 ^ height := by
  induction height with
  | zero => simp [owners]
  | succ height ih =>
      have disjoint : Disjoint ((owners height).image (false :: ·))
          ((owners height).image (true :: ·)) := by
        apply Finset.disjoint_left.mpr
        intro address left right
        obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp left
        obtain ⟨b, _, same⟩ := Finset.mem_image.mp right
        cases same
      have absent : ([] : Key) ∉ ((owners height).image (false :: ·) ∪
          (owners height).image (true :: ·)) := by simp
      rw [owners, Finset.card_insert_of_notMem absent, Finset.card_union_of_disjoint disjoint,
        Finset.card_image_of_injective _ (fun _ _ h => List.cons.inj h |>.2),
        Finset.card_image_of_injective _ (fun _ _ h => List.cons.inj h |>.2), pow_succ]
      omega

theorem nodeCost_le_primary (height : Nat) (state : State) (addresses : List Key) :
    nodeCost height state addresses ≤
      primaryCount (2 * height) (encode height state addresses) + (2 ^ height - 1) := by
  have bound := nodeCost_le_primary_add_nodes height state addresses
  have count := owners_card_add_one height
  omega

end MultiSplay.EndpointEncoding

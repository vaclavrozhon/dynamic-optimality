import VirtualLoserPreparation
import VirtualFiniteRelabel
import VirtualGrowingSlot

/-! Numerical lifting of the literal original strict Pass. Original
MatchingValid supplies every structural condition. Labels may be changed
arbitrarily subject to the new cap; no matching, source, destination,
Insert count, or persistent object is changed. -/

namespace Splay.Research.VirtualOriginalPassLift

open Splay.Interface Splay.Interface.MatchingValid
open Splay.Research.VirtualNumericInsertion Splay.Research.VirtualRetainedPass

/-- Changing only the numeric cap preserves the original structural Pass
certificate. The new state has exactly the original physical blocks. -/
theorem structural {n : ℕ} {oldParams params : Parameters} {physical shadow : State n}
    {id : ℕ} {source : Block n} {matching : List (Pairing n)}
    (sameShape : params.toShape = oldParams.toShape) (blocks : shadow.blocks = physical.blocks)
    (matchingValid : MatchingValid oldParams physical id source matching) :
    StructuralMatching params shadow id source matching := by
  refine ⟨matchingValid.1, matchingValid.2.1,
    fun pair member => (matchingValid.2.2.2.1 pair member).1, ?_, ?_⟩
  · intro pair member
    simpa only [State.block?, blocks] using (matchingValid.2.2.2.1 pair member).2.2.2
  · have exempt := congrArg Shape.exemptPasses sameShape
    have numerator := congrArg Shape.matchingNumerator sameShape
    have denominator := congrArg Shape.matchingDenominator sameShape
    simpa only [exempt, numerator, denominator] using matchingValid.2.2.2.2

noncomputable def events {n : ℕ} (shadow : State n) (id : ℕ) (source : Block n)
    (matching : List (Pairing n)) (target : Element n → ℕ) : List (Operation n) :=
  VirtualLoserPreparation.events shadow id matching ++
    VirtualFiniteRelabel.events (afterPass (VirtualLoserPreparation.lifted shadow matching) id source matching)
      target (List.finRange (2*n+1))

/-- The original literal Pass is the only structural operation emitted.
Upward variation is exactly preparation deficits plus actual subsequent
label rises, both computed at this same numeric checkpoint. -/
theorem realize {n : ℕ} {oldParams params : Parameters} {physical nextPhysical shadow : State n}
    (id : ℕ) (matching : List (Pairing n))
    (original : Step oldParams physical (.pass id matching) nextPhysical)
    (sameShape : params.toShape = oldParams.toShape) (blocks : shadow.blocks = physical.blocks)
    (valid : shadow.Valid params)
    (room : ∀ pair ∈ matching, shadow.value pair.winner+1 ≤ params.valueBound)
    (target : Element n → ℕ) (positive : ∀ element, 1 ≤ target element)
    (bounded : ∀ element, target element ≤ params.valueBound) :
    ∃ source,
      physical.blocks[id]? = some source ∧
      Trace params shadow (events shadow id source matching target) (State.mk nextPhysical.blocks target) ∧
      totalActivity (events shadow id source matching target) = matching.length ∧
      totalBlockGrowth (events shadow id source matching target) = 0 ∧
      totalInserts (events shadow id source matching target) = 0 ∧
      totalIncreases (events shadow id source matching target) =
        (matching.map (VirtualLoserPreparation.deficit shadow)).sum +
        ((List.finRange (2*n+1)).map fun element =>
          target element-(VirtualLoserPreparation.lifted shadow matching).value element).sum := by
  cases original.2.1 with
  | @pass _ _ source _ found matchingValid endpoint values =>
      have shape := structural sameShape blocks matchingValid
      have foundShadow : shadow.blocks[id]? = some source := by rw [blocks]; exact found
      obtain ⟨passTrace, passBlocks, passActivity, passGrowth, passInserts, passIncreases⟩ :=
        VirtualLoserPreparation.realize shadow id source matching valid foundShadow shape room
      let passed := afterPass (VirtualLoserPreparation.lifted shadow matching) id source matching
      have passedValid : passed.Valid params := VirtualGrowingSlot.trace_valid_after passTrace
      obtain ⟨normalization, normalizeIncreases, normalizeActivity, normalizeGrowth, normalizeInserts⟩ :=
        VirtualFiniteRelabel.realize passed target passedValid positive bounded
      have blockEndpoint : passed.blocks = nextPhysical.blocks := by
        rw [passBlocks]
        exact (congrArg (fun bs => Splay.Interface.passBlocks bs id source matching) blocks).trans endpoint.symm
      rw [blockEndpoint] at normalization
      dsimp only [passed] at normalizeIncreases normalizeActivity normalizeGrowth normalizeInserts
      refine ⟨source, found, trace_append passTrace normalization, ?_, ?_, ?_, ?_⟩
      · simp only [events, totalActivity_append, passActivity, normalizeActivity, Nat.add_zero]
      · simp only [events, totalBlockGrowth_append, passGrowth, normalizeGrowth, Nat.zero_add]
      · simp only [events, totalInserts_append, passInserts, normalizeInserts, Nat.zero_add]
      · simp only [events, totalIncreases_append, passIncreases]
        rw [normalizeIncreases]
        rfl

end Splay.Research.VirtualOriginalPassLift

#print axioms Splay.Research.VirtualOriginalPassLift.realize

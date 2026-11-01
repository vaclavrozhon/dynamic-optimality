import TangoSquared.DelayedChunkPayments
import TangoSquared.GadgetAggregation

/-! Direct bridges between actual projected layouts and gadget counts/potentials. -/

namespace TangoSquared

open Primary CyclicRuns Witnesses NormalizedWords

/-- On the fixed leaf universe, the partial projection is exactly the gadget's
owner filter followed by its specified fine-prefix map. -/
theorem gadgetProjection_word {H : Nat} {q : Gadget} {xs : List Key}
    (leaves : OnLeaves H xs) :
    xs.filterMap (gadgetProjection H q) = (ownerWord q.owner xs).map q.fine := by
  unfold gadgetProjection
  rw [fineProjection_word]
  apply List.map_congr_left
  intro x hx
  have hxH := leaves x (List.mem_filter.mp hx).1
  change x.take (min (q.split.hi + 1) H) = x.take (q.split.hi + 1)
  rw [← List.take_take, ← hxH, List.take_length]

/-- Exact cyclic return matching is inherited from the actual normalized four
periods, at the same rotated run layout used by entry and delayed payments. -/
theorem projectedLayout_returnsMatch {H : Nat} {q : Gadget} {xs : List Key}
    (hq : Valid H q) (initial : Key → Bool) (leaves : OnLeaves H xs)
    (normal : Normalized initial H (xs ++ (xs ++ (xs ++ xs))))
    (layout : CyclicLayout q.coarse (xs.filterMap (gadgetProjection H q))) :
    ReturnsMatch q.coarse (layout.first :: layout.rest) := by
  apply returnsMatch_of_returnWord q.coarse layout.first layout.rest
    layout.homogeneous layout.boundaries
  let runword := ((layout.first :: layout.rest).map Block.word).flatten
  have embed : (xs ++ (xs ++ (xs ++ xs))).filterMap (gadgetProjection H q) =
      layout.cutBefore ++ (runword ++ runword) ++
        (layout.suffix ++ xs.filterMap (gadgetProjection H q)) := by
    simp only [List.filterMap_append, runword, layout.rotation, layout.split, List.append_assoc]
  apply GapInheritance.returnWord_infix q.coarse layout.cutBefore _
    (layout.suffix ++ xs.filterMap (gadgetProjection H q))
  rw [← embed]
  apply gadgetProjection_returnWord hq initial _ normal
  intro x hx
  exact leaves x (by simpa using hx)

/-- The original finite demand count is bounded by the actual nontrivial run
occurrences in the canonical cyclic layout. -/
theorem projectedLayout_demand_le {H : Nat} {q : Gadget} {xs : List Key}
    (hq : q ∈ allGadgets H) (leaves : OnLeaves H xs)
    (layout : CyclicLayout q.coarse (xs.filterMap (gadgetProjection H q))) :
    q.count xs ≤ nontrivialRuns (layout.first :: layout.rest) := by
  rw [Gadget.count_eq_fine_demands hq xs, ← gadgetProjection_word leaves]
  convert layout.demands_le using 1
  congr 1

/-- The local turn identity uses the precise gadget telescoping term even when
the layout was constructed directly from the partial projected query word. -/
theorem projectedLayout_turn_identity {H : Nat} {q : Gadget} {xs : List Key}
    (hq : q ∈ allGadgets H) (leaves : OnLeaves H xs)
    (layout : CyclicLayout q.coarse (xs.filterMap (gadgetProjection H q)))
    (returns : ReturnsMatch q.coarse (layout.first :: layout.rest)) :
    (groupedJoins q.coarse (layout.first :: layout.rest) : ℤ) +
      (TurnAccounting.nontrivialMacroTurns (encode layout.first.first (layout.first :: layout.rest)) : ℤ) =
      q.potentialDifference H xs +
        (TurnAccounting.entryTurns (encode layout.first.first (layout.first :: layout.rest)) : ℤ) +
        (TurnAccounting.exitTurns (encode layout.first.first (layout.first :: layout.rest)) : ℤ) := by
  have h := local_turn_potential_identity q.coarse (fun _ _ h => take_mono_lex h _)
    layout.first layout.rest layout.homogeneous layout.boundaries returns
  have hp : localTurnPotential q.coarse ((layout.first :: layout.rest).map Block.word).flatten =
      q.potentialDifference H xs := by
    rw [layout.rotation, localTurnPotential_swap_append, ← layout.split, gadgetProjection_word leaves,
      ← Gadget.potentialDifference_eq_local hq xs leaves]
  rw [hp] at h
  exact h

end TangoSquared

import MultiSplay.PlaceMove

/-! # A finite physical program constructs its own global accounting universe -/

noncomputable section

namespace MultiSplay.Unlocated

open Splay.Interface (Parameters)

variable {m limit : Nat} {params : Parameters} {slack depth : Nat}

theorem Program.place {before after : List Trees} (program : Program params slack depth before after)
    (placement : Placement m limit before) (fits : limit + program.joins ≤ 2*m+1) :
    ∃ result : Placement m (limit+program.joins) after,
      ∃ compiled : PackedSplay.Program params slack depth (placement.locations.map Location.packed) (result.locations.map Location.packed),
        compiled.splayCost = program.splayCost ∧ compiled.requests = program.requests ∧
        compiled.rotations = program.rotations ∧ compiled.boundaries = program.boundaries := by
  induction program generalizing limit with
  | done forest => exact ⟨placement, .done _, rfl, rfl, rfl, rfl⟩
  | next move tail ih =>
      obtain ⟨middle, step, headCost, headRequests, headRotations, headBoundaries⟩ := move.place placement
        (by change limit+(move.joins+tail.joins) ≤ _ at fits; omega)
      obtain ⟨result, compiled, tailCost, tailRequests, tailRotations, tailBoundaries⟩ := ih middle
        (by change limit+(move.joins+tail.joins) ≤ _ at fits; omega)
      let final : Placement m (limit + (move.joins + tail.joins)) _ :=
        {result with bounded := by simpa only [LocatedBelow, Nat.add_assoc] using result.bounded}
      exact ⟨final, .next step compiled, congrArg₂ Nat.add headCost tailCost,
        congrArg₂ Nat.add headRequests tailRequests, congrArg₂ Nat.add headRotations tailRotations,
        congrArg₂ Nat.add headBoundaries tailBoundaries⟩

/-- Reserve at most one fresh element per join. The cost theorem charges only
the initially active mass: every reserved element starts at neutral value one. -/
theorem Program.exists_packed {before after : List Trees} (program : Program params slack depth before after) :
    ∃ m : Nat, ∃ initial : Placement m (mass before) before,
      ∃ final : Placement m (mass before + program.joins) after,
      ∃ compiled : PackedSplay.Program params slack depth (initial.locations.map Location.packed) (final.locations.map Location.packed),
        compiled.splayCost = program.splayCost ∧ compiled.requests = program.requests ∧
        compiled.rotations = program.rotations ∧ compiled.boundaries = program.boundaries := by
  let space := mass before + program.joins
  obtain ⟨initial⟩ := initial_placement (m := space) before (by dsimp [space]; omega)
  obtain ⟨final, compiled, cost, requests, rotations, boundaries⟩ := program.place initial (by dsimp [space]; omega)
  exact ⟨space, initial, final, compiled, cost, requests, rotations, boundaries⟩

end MultiSplay.Unlocated

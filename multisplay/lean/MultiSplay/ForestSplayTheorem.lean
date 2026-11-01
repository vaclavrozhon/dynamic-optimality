import MultiSplay.PlaceProgram
import MultiSplay.PortableSplayFactor

/-!
# Forest splay comparison without any accounting-history or placement premise

The physical program contains only local comparison trees, actual complete
splay executions, comparison rotations, and common-root splits and joins.
Both the finite global universe and the complete persistent rich history are
constructed by the proof. In particular a join accepts arbitrary current
children; their embeddings need not be supplied or made compatible by a caller.
-/

namespace MultiSplay.Unlocated

open Splay.Interface (Parameters Shape)
open Splay.Rank (Snapshot)
open Splay.Accounting (articleParameters)

variable {params : Parameters} {slack depth : Nat} {before after : List Trees}

def Program.volume (program : Program params slack depth before after) : Nat :=
  mass before + program.requests + program.rotations + program.boundaries

/-- The uniform original black-box factor. All accounting and placement data
are constructed, and no additive charge depends on the number of reserved slots. -/
theorem splay_bound (shape : Shape) (slack depth : Nat) :
    ∃ constant : Nat, 0 < constant ∧ ∀ params : Parameters, params.toShape = shape →
      2 ≤ params.growingLimit → params.exemptPasses = 2 →
      params.matchingNumerator = 1 → params.matchingDenominator = 8 →
      ∀ {before after : List Trees} (program : Program params slack depth before after),
        (∀ trees ∈ before, Splay.Analysis.contractedGap
          (Snapshot.ofTree trees.comparison).withTruePriority.maxRank ≤ params.valueBound) →
        program.splayCost + program.boundaries ≤ constant * program.volume *
          params.valueBound * (Nat.clog 2 params.valueBound + 1)^2 := by
  obtain ⟨constant, positive, bound⟩ := PackedSplay.splay_bound shape slack depth
  refine ⟨constant, positive, ?_⟩
  intro params same growing exempt numerator denominator before after program cap
  obtain ⟨m, initial, final, compiled, cost, requests, rotations, boundaries⟩ := program.exists_packed
  have cap' : ∀ trees ∈ initial.locations.map Location.packed,
      Splay.Analysis.contractedGap (Snapshot.ofTree trees.comparison).withTruePriority.maxRank ≤ params.valueBound := by
    intro trees member
    obtain ⟨location, present, rfl⟩ := List.mem_map.mp member
    exact cap location.1 (initial.shapes ▸ List.mem_map.mpr ⟨location, present, rfl⟩)
  have paid := bound params same growing exempt numerator denominator compiled
    (packed_separate initial.locations initial.separate) cap'
  have volume : compiled.volume = program.volume := by
    unfold PackedSplay.Program.volume Program.volume
    rw [packed_mass, initial.shapes, requests, rotations, boundaries]
  rwa [cost, boundaries, volume] at paid

/-- The capacity form used by multi-splay. The input contains no global
embedding, passive-frame oracle, interface trace, or amortized-cost hypothesis. -/
theorem normalized_splay_bound (slack depth : Nat) :
    ∃ constant : Nat, 0 < constant ∧ ∀ (capacity : Nat) {before after : List Trees}
      (program : Program (articleParameters (Layered.Bounded.height capacity)) slack depth before after),
      (∀ trees ∈ before, trees.comparison.height ≤ Layered.Bounded.height capacity) →
      program.splayCost + program.boundaries ≤ constant * program.volume * Splay.Analysis.targetFactor capacity := by
  obtain ⟨constant, positive, bound⟩ := PackedSplay.normalized_splay_bound slack depth
  refine ⟨constant, positive, ?_⟩
  intro capacity before after program bounded
  obtain ⟨m, initial, final, compiled, cost, requests, rotations, boundaries⟩ := program.exists_packed
  have heights : ∀ trees ∈ initial.locations.map Location.packed,
      trees.comparison.height ≤ Layered.Bounded.height capacity := by
    intro trees member
    obtain ⟨location, present, rfl⟩ := List.mem_map.mp member
    exact bounded location.1 (initial.shapes ▸ List.mem_map.mpr ⟨location, present, rfl⟩)
  have paid := bound capacity compiled (packed_separate initial.locations initial.separate) heights
  have volume : compiled.volume = program.volume := by
    unfold PackedSplay.Program.volume Program.volume
    rw [packed_mass, initial.shapes, requests, rotations, boundaries]
  rwa [cost, boundaries, volume] at paid

end MultiSplay.Unlocated

import TangoSquared.Paper20261030.LocalContextScriptSpace
import TangoSquared.Paper20261030.MultiSourceSingleCursor
import TangoSquared.Paper20261030.MultiSourceAugment

/-! The eight-block reassembly kernel in the shared physical tree. The
selected finger returns to the context root and every other finger stays
valid. Extra metadata is retained at physical vertices by locally reading
it before a write. Retention alone does not assert the semantic correctness
of cached header fields after the head switch.
-/

namespace TangoSquared.Paper20261030.HeadBlocks.Shared

open ColoredStorage SourcePointer ProjectionLocal OrderedContext MultiSourceProgram

variable {α ρ μ F : Type*} [DecidableEq F]

def program (finger : F) : Program
    (MultiSourceAugment.State (Option (LocalRecordActions.State ρ)) F (List ρ) μ) F (List ρ × μ) :=
  MultiSourceAugment.program (MultiSourceSingleCursor.program LocalRecordActions.program finger)

theorem run (finger : F) (oldRight : Bool) (bits : Fin 8 → Bool) (blocks : Fin 8 → Projected α ρ)
    (known : ∀ key, bits key = (blocks key).isSome)
    (oldRecords newRecords : List Bool → List ρ) (initial final : Source α (List ρ))
    (oldTree : decorated blocks (recordContext oldRecords [] (before oldRight)) = some initial)
    (newTree : decorated blocks (recordContext newRecords [] (after oldRight)) = some final)
    (outside : List (Frame α (List ρ))) (config : Configuration F α (List ρ × μ))
    (positioned : MultiSourceSingleCursor.Represents finger ⟨initial,outside⟩ (config.mapRecords Prod.fst))
    (valid : WellFormed config) :
    ∃ target reads cost,
      Run (program finger) (.ready (some (.ready (Local.actions oldRight bits oldRecords newRecords)))) config
        (.ready (some (.ready []))) target reads cost ∧
      MultiSourceSingleCursor.Represents finger ⟨final,outside⟩ (target.mapRecords Prod.fst) ∧
      WellFormed target ∧ target.tree.inventory Prod.snd = config.tree.inventory Prod.snd ∧ cost ≤ 576 := by
  obtain ⟨plainReads,plainCost,plainRun,bound⟩ :=
    Local.run oldRight bits blocks known oldRecords newRecords initial final oldTree newTree outside
  obtain ⟨plainTarget,sharedRun,sharedRep⟩ :=
    MultiSourceSingleCursor.compile_run LocalRecordActions.program finger plainRun (config.mapRecords Prod.fst) positioned
  obtain ⟨target,reads,cost,actual,erases,metadata,bounded⟩ := MultiSourceAugment.compile_run sharedRun config rfl
  refine ⟨target,reads,cost,actual,?_,actual.wellFormed valid,metadata,by omega⟩
  rw [erases]
  exact sharedRep

end TangoSquared.Paper20261030.HeadBlocks.Shared

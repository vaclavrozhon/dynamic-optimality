import ChaCha.Paper20261030.ComponentBoundaryWriteLabels
import ChaCha.Paper20261030.MultiSourceWriteLabelComposition
import ChaCha.Paper20261030.ComponentBoundaryContinuation
import ChaCha.Paper20261030.ComponentRootRegister
import ChaCha.Paper20261030.MultiSourceFinish
import ChaCha.Paper20261030.ThreeColorLayoutStability
import ChaCha.Paper20261030.ComponentOriginalKeys

set_option autoImplicit false

/-!
# Continuing a component operation with actual boundary observations

The preparation compiler's final scalar root register initializes the
boundary observer. The transition retains no source tree, fragment, or
operation history. Its boundary values are obtained by the charged
observer; its final forest again has the canonical three-color layout.
-/

namespace ChaCha.Paper20261030.ComponentBoundaryContinuation

open ColoredStorage SourcePointer Structural PhysicalForestMetadata LocalComponentForestCompiler
open LocalComponentCompiler ForestConnector.ThreeColors

variable {α β ρ ι η σ : Type*} [DecidableEq α] [DecidableEq ι] [DecidableEq η]

local instance : LinearOrder (Option Bool) := inferInstanceAs (LinearOrder (WithBot Bool))

theorem active_labels (source : SourceLocalProgram.Program σ ρ) (start last : σ) (oldId : η)
    (color : α → Option Bool) (low high terminal : η × ρ) (key : α) (head tail : Source α (η × ρ))
    (logicalUnique : ((Source.fork low head (.fork high (.leaf key terminal) tail)).inventory Prod.fst).Nodup)
    (forest : TaggedForest (Option Bool) α (LocalColoredCompiler.LogicalRecord ρ η (Option Bool)) ι)
    (represented : ProjectionForest.Represents color
      ⟨annotate Prod.fst color none (.fork low head (.fork high (.leaf key terminal) tail)),[]⟩ (erase forest))
    (physicalUnique : Unique forest) (headerKey : α)
    (payload : Option Bool → α → Source β (List (Option (PhysicalDatum α ρ ι η (Option Bool)))))
    (before current : MultiSourceProgram.Configuration (Option Bool) β (List (Option (PhysicalDatum α ρ ι η (Option Bool)))))
    {frontReads frontCost}
    (front : MultiSourceWriteLabels.Run (List.map physicalLabel) (LocalComponentCompiler.program source none wingOrientation)
      (ready start oldId) before (ready last low.1) current frontReads frontCost)
    (assembled : ForestConnector.assemble (representation none wingOrientation headerKey payload forest)
      (layout (representation none wingOrientation headerKey payload forest)) = some current) :
    ∃ finalForest finalConfig reads cost,
      MultiSourceWriteLabels.Run (List.map physicalLabel) (program source true oldId) (initial source true oldId start) before
        (.second low.1 (ComponentObserverCompiler.ready
          (BoundaryReadController.activeResult Prod.fst color low high terminal key head tail) low.1)) finalConfig reads cost ∧
      ProjectionForest.Represents color
        ⟨annotate Prod.fst color none (.fork low head (.fork high (.leaf key terminal) tail)),[]⟩ (erase finalForest) ∧
      Unique finalForest ∧
      ForestConnector.assemble (representation none wingOrientation headerKey payload finalForest)
        (layout (representation none wingOrientation headerKey payload finalForest)) = some finalConfig ∧
      (∀ q, (representation none wingOrientation headerKey payload finalForest q).isSome =
        (representation none wingOrientation headerKey payload forest q).isSome) ∧
      MultiSourceProgram.WellFormed finalConfig ∧ cost ≤ frontCost+87360 := by
  let physical := representation none wingOrientation headerKey payload forest
  obtain ⟨finalForest,finalConfig,reads,cost,observed,finalRep,finalUnique,finalAssembly,covered,valid,bound⟩ :=
    ComponentBoundaryReadController.active_labels color low high terminal key head tail logicalUnique forest represented physicalUnique
      none wingOrientation headerKey payload (layout physical) (distinct physical) (covers physical) current assembled
  have presence := ForestConnector.same_presence (layout physical) physical
    (representation none wingOrientation headerKey payload finalForest) current finalConfig assembled finalAssembly (covers physical) covered
  have actual := MultiSourceFinish.finish_labels (select oldId) (observerInitial true)
    (fun _ => ComponentBoundaryReadController.program none wingOrientation) front observed
  refine ⟨finalForest,finalConfig,_,_,actual,finalRep,finalUnique,?_,presence,valid,?_⟩
  · rw [layout_congr physical (representation none wingOrientation headerKey payload finalForest) presence]
    exact finalAssembly
  · have limit : cost ≤ 87360 := by simpa only [Fintype.card_option,Fintype.card_bool] using bound
    omega

theorem sentinel_labels (source : SourceLocalProgram.Program σ ρ) (start last : σ) (oldId : η)
    (color : α → Option Bool) (high terminal : η × ρ) (key : α) (tail : Source α (η × ρ))
    (logicalUnique : ((Source.fork high (.leaf key terminal) tail).inventory Prod.fst).Nodup)
    (forest : TaggedForest (Option Bool) α (LocalColoredCompiler.LogicalRecord ρ η (Option Bool)) ι)
    (represented : ProjectionForest.Represents color
      ⟨annotate Prod.fst color none (.fork high (.leaf key terminal) tail),[]⟩ (erase forest))
    (physicalUnique : Unique forest) (headerKey : α)
    (payload : Option Bool → α → Source β (List (Option (PhysicalDatum α ρ ι η (Option Bool)))))
    (before current : MultiSourceProgram.Configuration (Option Bool) β (List (Option (PhysicalDatum α ρ ι η (Option Bool)))))
    {frontReads frontCost}
    (front : MultiSourceWriteLabels.Run (List.map physicalLabel) (LocalComponentCompiler.program source none wingOrientation)
      (ready start oldId) before (ready last high.1) current frontReads frontCost)
    (assembled : ForestConnector.assemble (representation none wingOrientation headerKey payload forest)
      (layout (representation none wingOrientation headerKey payload forest)) = some current) :
    ∃ finalForest finalConfig reads cost,
      MultiSourceWriteLabels.Run (List.map physicalLabel) (program source false oldId) (initial source false oldId start) before
        (.second high.1 (ComponentObserverCompiler.ready
          (BoundaryReadController.sentinelResult Prod.fst color high terminal key tail) high.1)) finalConfig reads cost ∧
      ProjectionForest.Represents color
        ⟨annotate Prod.fst color none (.fork high (.leaf key terminal) tail),[]⟩ (erase finalForest) ∧
      Unique finalForest ∧
      ForestConnector.assemble (representation none wingOrientation headerKey payload finalForest)
        (layout (representation none wingOrientation headerKey payload finalForest)) = some finalConfig ∧
      (∀ q, (representation none wingOrientation headerKey payload finalForest q).isSome =
        (representation none wingOrientation headerKey payload forest q).isSome) ∧
      MultiSourceProgram.WellFormed finalConfig ∧ cost ≤ frontCost+49920 := by
  let physical := representation none wingOrientation headerKey payload forest
  obtain ⟨finalForest,finalConfig,reads,cost,observed,finalRep,finalUnique,finalAssembly,covered,valid,bound⟩ :=
    ComponentBoundaryReadController.sentinel_labels color high terminal key tail logicalUnique forest represented physicalUnique
      none wingOrientation headerKey payload (layout physical) (distinct physical) (covers physical) current assembled
  have presence := ForestConnector.same_presence (layout physical) physical
    (representation none wingOrientation headerKey payload finalForest) current finalConfig assembled finalAssembly (covers physical) covered
  have actual := MultiSourceFinish.finish_labels (select oldId) (observerInitial false)
    (fun _ => ComponentBoundaryReadController.program none wingOrientation) front observed
  refine ⟨finalForest,finalConfig,_,_,actual,finalRep,finalUnique,?_,presence,valid,?_⟩
  · rw [layout_congr physical (representation none wingOrientation headerKey payload finalForest) presence]
    exact finalAssembly
  · have limit : cost ≤ 49920 := by simpa only [Fintype.card_option,Fintype.card_bool] using bound
    omega

end ChaCha.Paper20261030.ComponentBoundaryContinuation

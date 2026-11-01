import TangoSquared.Paper20261030.LocalComponentBoundaryRead
import TangoSquared.Paper20261030.ComponentRootRegister
import TangoSquared.Paper20261030.MultiSourceFinish
import TangoSquared.Paper20261030.ThreeColorLayoutStability
import TangoSquared.Paper20261030.ComponentOriginalKeys

set_option autoImplicit false

/-!
# Continuing a component operation with actual boundary observations

The preparation compiler's final scalar root register initializes the
boundary observer. The transition retains no source tree, fragment, or
operation history. Its boundary values are obtained by the charged
observer; its final forest again has the canonical three-color layout.
-/

namespace TangoSquared.Paper20261030.ComponentBoundaryContinuation

open ColoredStorage SourcePointer Structural PhysicalForestMetadata LocalComponentForestCompiler
open LocalComponentCompiler ForestConnector.ThreeColors

variable {α β ρ ι η σ : Type*} [DecidableEq α] [DecidableEq ι] [DecidableEq η]

local instance : LinearOrder (Option Bool) := inferInstanceAs (LinearOrder (WithBot Bool))

def select (fallback : η) (state : LocalComponentForestCompiler.State σ α ρ ι η (Option Bool)) : η :=
  (rootRegister state).getD fallback

def observerInitial (prefixPresent : Bool) (ident : η) : ComponentBoundaryReadController.State α ρ ι η (Option Bool) :=
  ComponentObserverCompiler.ready (if prefixPresent then .start else .readHigh none) ident

def program (source : SourceLocalProgram.Program σ ρ) (prefixPresent : Bool) (fallback : η) :=
  MultiSourceFinish.program (LocalComponentCompiler.program (α := α) (ι := ι) source none wingOrientation)
    (select fallback) (observerInitial prefixPresent) (fun _ => ComponentBoundaryReadController.program none wingOrientation)

def initial (source : SourceLocalProgram.Program σ ρ) (prefixPresent : Bool) (fallback : η) (state : σ) :=
  MultiSourceFinish.enter (LocalComponentCompiler.program (α := α) (ι := ι) source none wingOrientation)
    (select fallback) (observerInitial (α := α) (ρ := ρ) (ι := ι) prefixPresent) (ready state fallback)

theorem active (source : SourceLocalProgram.Program σ ρ) (start last : σ) (oldId : η)
    (color : α → Option Bool) (low high terminal : η × ρ) (key : α) (head tail : Source α (η × ρ))
    (logicalUnique : ((Source.fork low head (.fork high (.leaf key terminal) tail)).inventory Prod.fst).Nodup)
    (forest : TaggedForest (Option Bool) α (LocalColoredCompiler.LogicalRecord ρ η (Option Bool)) ι)
    (represented : ProjectionForest.Represents color
      ⟨annotate Prod.fst color none (.fork low head (.fork high (.leaf key terminal) tail)),[]⟩ (erase forest))
    (physicalUnique : Unique forest) (headerKey : α)
    (payload : Option Bool → α → Source β (List (Option (PhysicalDatum α ρ ι η (Option Bool)))))
    (before current : MultiSourceProgram.Configuration (Option Bool) β (List (Option (PhysicalDatum α ρ ι η (Option Bool)))))
    {frontReads frontCost}
    (front : MultiSourceProgram.Run (LocalComponentCompiler.program source none wingOrientation)
      (ready start oldId) before (ready last low.1) current frontReads frontCost)
    (assembled : ForestConnector.assemble (representation none wingOrientation headerKey payload forest)
      (layout (representation none wingOrientation headerKey payload forest)) = some current) :
    ∃ finalForest finalConfig reads cost,
      MultiSourceProgram.Run (program source true oldId) (initial source true oldId start) before
        (.second low.1 (ComponentObserverCompiler.ready
          (BoundaryReadController.activeResult Prod.fst color low high terminal key head tail) low.1)) finalConfig reads cost ∧
      ProjectionForest.Represents color
        ⟨annotate Prod.fst color none (.fork low head (.fork high (.leaf key terminal) tail)),[]⟩ (erase finalForest) ∧
      Unique finalForest ∧
      ForestConnector.assemble (representation none wingOrientation headerKey payload finalForest)
        (layout (representation none wingOrientation headerKey payload finalForest)) = some finalConfig ∧
      MultiSourceProgram.WellFormed finalConfig ∧ cost ≤ frontCost+87360 := by
  let physical := representation none wingOrientation headerKey payload forest
  obtain ⟨finalForest,finalConfig,reads,cost,observed,finalRep,finalUnique,finalAssembly,covered,valid,bound⟩ :=
    ComponentBoundaryReadController.active color low high terminal key head tail logicalUnique forest represented physicalUnique
      none wingOrientation headerKey payload (layout physical) (distinct physical) (covers physical) current assembled
  have presence := ForestConnector.same_presence (layout physical) physical
    (representation none wingOrientation headerKey payload finalForest) current finalConfig assembled finalAssembly (covers physical) covered
  have actual := MultiSourceFinish.finish (select oldId) (observerInitial true)
    (fun _ => ComponentBoundaryReadController.program none wingOrientation) front observed
  refine ⟨finalForest,finalConfig,_,_,actual,finalRep,finalUnique,?_,valid,?_⟩
  · rw [layout_congr physical (representation none wingOrientation headerKey payload finalForest) presence]
    exact finalAssembly
  · have limit : cost ≤ 87360 := by simpa only [Fintype.card_option,Fintype.card_bool] using bound
    omega

theorem sentinel (source : SourceLocalProgram.Program σ ρ) (start last : σ) (oldId : η)
    (color : α → Option Bool) (high terminal : η × ρ) (key : α) (tail : Source α (η × ρ))
    (logicalUnique : ((Source.fork high (.leaf key terminal) tail).inventory Prod.fst).Nodup)
    (forest : TaggedForest (Option Bool) α (LocalColoredCompiler.LogicalRecord ρ η (Option Bool)) ι)
    (represented : ProjectionForest.Represents color
      ⟨annotate Prod.fst color none (.fork high (.leaf key terminal) tail),[]⟩ (erase forest))
    (physicalUnique : Unique forest) (headerKey : α)
    (payload : Option Bool → α → Source β (List (Option (PhysicalDatum α ρ ι η (Option Bool)))))
    (before current : MultiSourceProgram.Configuration (Option Bool) β (List (Option (PhysicalDatum α ρ ι η (Option Bool)))))
    {frontReads frontCost}
    (front : MultiSourceProgram.Run (LocalComponentCompiler.program source none wingOrientation)
      (ready start oldId) before (ready last high.1) current frontReads frontCost)
    (assembled : ForestConnector.assemble (representation none wingOrientation headerKey payload forest)
      (layout (representation none wingOrientation headerKey payload forest)) = some current) :
    ∃ finalForest finalConfig reads cost,
      MultiSourceProgram.Run (program source false oldId) (initial source false oldId start) before
        (.second high.1 (ComponentObserverCompiler.ready
          (BoundaryReadController.sentinelResult Prod.fst color high terminal key tail) high.1)) finalConfig reads cost ∧
      ProjectionForest.Represents color
        ⟨annotate Prod.fst color none (.fork high (.leaf key terminal) tail),[]⟩ (erase finalForest) ∧
      Unique finalForest ∧
      ForestConnector.assemble (representation none wingOrientation headerKey payload finalForest)
        (layout (representation none wingOrientation headerKey payload finalForest)) = some finalConfig ∧
      MultiSourceProgram.WellFormed finalConfig ∧ cost ≤ frontCost+49920 := by
  let physical := representation none wingOrientation headerKey payload forest
  obtain ⟨finalForest,finalConfig,reads,cost,observed,finalRep,finalUnique,finalAssembly,covered,valid,bound⟩ :=
    ComponentBoundaryReadController.sentinel color high terminal key tail logicalUnique forest represented physicalUnique
      none wingOrientation headerKey payload (layout physical) (distinct physical) (covers physical) current assembled
  have presence := ForestConnector.same_presence (layout physical) physical
    (representation none wingOrientation headerKey payload finalForest) current finalConfig assembled finalAssembly (covers physical) covered
  have actual := MultiSourceFinish.finish (select oldId) (observerInitial false)
    (fun _ => ComponentBoundaryReadController.program none wingOrientation) front observed
  refine ⟨finalForest,finalConfig,_,_,actual,finalRep,finalUnique,?_,valid,?_⟩
  · rw [layout_congr physical (representation none wingOrientation headerKey payload finalForest) presence]
    exact finalAssembly
  · have limit : cost ≤ 49920 := by simpa only [Fintype.card_option,Fintype.card_bool] using bound
    omega

end TangoSquared.Paper20261030.ComponentBoundaryContinuation
